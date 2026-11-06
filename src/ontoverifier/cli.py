"""Prove things about ontologies, and about how they change."""

import argparse
import json
import sys
from pathlib import Path

from ontoverifier import language, versions
from ontoverifier.axioms import Axiom, load
from ontoverifier.verifier import Verifier


def _load(args):
    return load(*args.files, alignments=getattr(args, "alignment", None) or ())


def _common(parser):
    parser.add_argument("--out", default="out")
    parser.add_argument("--no-kernel", action="store_true",
                        help="reason only: fast, with nothing checked by Lean")


def main(argv=None):
    parser = argparse.ArgumentParser(prog="ontoverifier", description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)

    one = commands.add_parser("check", help="every class, and the data if there is any")
    one.add_argument("files", nargs="+")
    one.add_argument("--alignment", action="append")
    one.add_argument("--witnesses", type=int, help="certify this many satisfiable classes")
    _common(one)

    entails = commands.add_parser("entails", help="does a claim follow? e.g. sub A B, some A p B")
    entails.add_argument("files", nargs="+")
    entails.add_argument("--claim", nargs="+", required=True, metavar="TERM",
                         help="sub A B | disjoint A B | some A p B | all A p B, as full IRIs")
    _common(entails)

    query = commands.add_parser("query", help="must a SPARQL query be empty on every graph?")
    query.add_argument("files", nargs="+")
    query.add_argument("--sparql", required=True, help="a file holding the query")
    _common(query)

    gate = commands.add_parser("gate", help="what changes in meaning between two versions")
    gate.add_argument("--old", nargs="+", required=True)
    gate.add_argument("--new", nargs="+", required=True)
    gate.add_argument("--new-alignment", action="append")
    gate.add_argument("--strict", action="store_true", help="also block on lost subsumptions")
    gate.add_argument("--limit", type=int, default=50, help="facts to certify per list")
    _common(gate)

    history = commands.add_parser("history", help="each version against the one before it")
    history.add_argument("files", nargs="+")
    history.add_argument("--limit", type=int, default=50)
    _common(history)

    comments = commands.add_parser("comments", help="do the definitions agree with the axioms?")
    comments.add_argument("files", nargs="+")
    comments.add_argument("--alignment", action="append")
    comments.add_argument("--model", required=True, help="ollama:<name> or command:<program>")
    comments.add_argument("--limit", type=int, help="a seeded sample of this many definitions")
    comments.add_argument("--seed", type=int, default=0)
    comments.add_argument("--near-disjoint", action="store_true",
                          help="only classes under a disjointness axiom, which can contradict")
    _common(comments)

    args = parser.parse_args(argv)
    certify = not args.no_kernel
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    if args.command == "check":
        report = Verifier(_load(args), out, certify).check(args.witnesses)
        _write(out / "report.json", report)
        print(summary(report))
        return 1 if report["unsatisfiable"] or report["consistent"] is False else 0

    if args.command == "entails":
        kind, *terms = args.claim
        verifier = Verifier(_load(args), out, certify)
        finding = verifier.judge(Axiom(kind, tuple(terms)))
        verifier.finish()
        print(json.dumps(finding.as_dict(), indent=1, ensure_ascii=False))
        return 0 if finding.verdict == "entailed" else 1

    if args.command == "query":
        verifier = Verifier(_load(args), out, certify)
        finding = verifier.query(Path(args.sparql).read_text())
        verifier.finish()
        print(json.dumps(finding.as_dict(), indent=1, ensure_ascii=False))
        return 0

    if args.command == "gate":
        old = load(*args.old)
        new = load(*args.new, alignments=args.new_alignment or ())
        change = versions.compare(old, new, out, certify, args.limit)
        _write(out / "gate.json", change.as_dict(args.strict))
        print(gate_summary(change, args.strict))
        return 1 if change.blocked(args.strict) or change.rejected() else 0

    if args.command == "history":
        steps = versions.history([load(f) for f in args.files], out, certify, args.limit)
        _write(out / "history.json", [s.as_dict() for s in steps])
        for step in steps:
            print(gate_summary(step))
        return 1 if any(s.blocked() for s in steps) else 0

    model = language.Cached(language.model_for(args.model), out / "answers.json")

    def progress(done, total, reading):
        print(f"\r{done}/{total}", end="", file=sys.stderr, flush=True)

    theory = _load(args)
    only = language.near_disjoint(theory) if args.near_disjoint else None
    result, _ = language.read_definitions(theory, model, out, certify, args.limit, args.seed,
                                          only=only, progress=progress)
    print(file=sys.stderr)
    _write(out / "comments.json", result)
    (out / "comments.md").write_text(language.markdown(result))
    print(f"{result['definitions']} definitions, {result['with_claims']} with claims: "
          f"{result['verdicts']}\nWritten to {out / 'comments.md'}")
    return 0


def _write(path, value):
    path.write_text(json.dumps(value, indent=1, ensure_ascii=False))


def summary(report):
    lines = [report["source"],
             f"  {report['axioms']} axioms translated, {report['coverage']:.0%} of what was read"]
    for reason, count in sorted(report["not_translated"].items(), key=lambda x: -x[1]):
        lines.append(f"    not translated: {count} {reason}")
    lines.append(f"  {report['classes']} classes, {report['unsatisfiable']} unsatisfiable, "
                 f"{report['out_of_budget']} out of budget")
    consistent = {True: "no clash found", False: "NO", None: "unknown, out of budget"}
    lines.append(f"  data: {consistent[report['consistent']]}")
    for item in report["counts"]:
        lines.append(f"  {item['kind']} ({item['verdict']}): {item['count']}, "
                     f"kernel {item['kernel']}")
    return "\n".join(lines)


def gate_summary(change, strict=False):
    status = "BLOCKED" if change.blocked(strict) else "ok"
    lines = [f"{change.old} -> {change.new}: {status}",
             f"  axioms: +{len(change.added)} -{len(change.removed)}",
             f"  new unsatisfiable classes: {len(change.new_unsatisfiable)}",
             f"  new data clashes: {len(change.new_clashes)}",
             f"  subsumptions: {change.lost_total} lost, {change.gained_total} gained",
             f"  theorems: {change.kernel}"]
    for item in change.new_unsatisfiable[:5]:
        lines.append(f"    {item['claim']} [{item['kernel']}]")
        lines.append(f"      from the change: {item['added_axioms_used']}")
    return "\n".join(lines)


if __name__ == "__main__":
    sys.exit(main())
