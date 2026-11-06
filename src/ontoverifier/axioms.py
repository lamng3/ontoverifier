"""The fragment of OWL that OntoVerifier translates, read from RDF.

An axiom is one first-order sentence. Everything else in the file is counted in
`Theory.skipped` and never silently dropped: leaving an axiom out keeps a proof
of unsatisfiability valid (the rest of the ontology can only add consequences)
but it can make a witness wrong, because the dropped axiom may fail in it. So a
witness only speaks for the fragment, and the report says how much that covers.
"""

import re
from collections import Counter, defaultdict
from dataclasses import dataclass, field

from rdflib import BNode, Graph, Literal, OWL, RDF, RDFS, URIRef
from rdflib.collection import Collection

DEFINITIONS = (
    URIRef("http://purl.obolibrary.org/obo/IAO_0000115"),
    URIRef("http://www.w3.org/2004/02/skos/core#definition"),
    RDFS.comment,
)
SKOS_LABEL = URIRef("http://www.w3.org/2004/02/skos/core#prefLabel")
# OBO ontologies import these relations and often ship without their labels.
OBO_RELATIONS = {
    "BFO_0000050": "part of", "BFO_0000051": "has part", "BFO_0000066": "occurs in",
    "RO_0000057": "has participant", "RO_0000086": "has quality",
    "RO_0001000": "derives from", "RO_0001025": "located in", "RO_0002131": "overlaps",
    "RO_0002220": "adjacent to", "RO_0002233": "has input", "RO_0002234": "has output",
    "RO_0002354": "formed as result of", "RO_0002473": "composed primarily of",
}

# kind -> how the sentence reads, for reports.
KINDS = {
    "sub": "{0} ⊑ {1}",
    "disjoint": "{0} ⊓ {1} ⊑ ⊥",
    "nothing": "{0} ⊑ ⊥",
    "domain": "∃{0}.⊤ ⊑ {1}",
    "range": "⊤ ⊑ ∀{0}.{1}",
    "subprop": "{0} ⊑ {1}",
    "inverse": "{0} ⊑ {1}⁻",
    "symmetric": "{0} ⊑ {0}⁻",
    "transitive": "{0} ∘ {0} ⊑ {0}",
    "some": "{0} ⊑ ∃{1}.{2}",
    "all": "{0} ⊑ ∀{1}.{2}",
    "type": "{1}({0})",
    "rel": "{1}({0}, {2})",
}
_SKIP_TYPES = {OWL.Class, OWL.ObjectProperty, OWL.DatatypeProperty, OWL.AnnotationProperty,
               OWL.Ontology, OWL.NamedIndividual, OWL.Restriction, RDFS.Class, RDF.Property,
               OWL.Thing, OWL.AllDisjointClasses, OWL.AllDifferent, OWL.Axiom}


@dataclass(frozen=True)
class Axiom:
    kind: str
    args: tuple

    def text(self, short=None):
        short = short or local
        return KINDS[self.kind].format(*(short(a) for a in self.args))


@dataclass
class Theory:
    axioms: list = field(default_factory=list)
    skipped: Counter = field(default_factory=Counter)
    classes: set = field(default_factory=set)
    individuals: set = field(default_factory=set)
    properties: set = field(default_factory=set)
    labels: dict = field(default_factory=dict)
    definitions: dict = field(default_factory=dict)
    source: str = ""

    def add(self, kind, *args):
        axiom = Axiom(kind, tuple(str(a) for a in args))
        if axiom not in self._seen:
            self._seen.add(axiom)
            self.axioms.append(axiom)
            self.index[kind].append(axiom)

    def __post_init__(self):
        self._seen = set()
        self.index = defaultdict(list)

    @property
    def translated(self):
        return len(self.axioms)

    @property
    def terminology(self):
        """The axioms about classes and properties, without the data."""
        return [a for a in self.axioms if a.kind not in ("type", "rel")]

    def extended(self, *axioms):
        """A copy with more axioms. Nothing about this theory changes."""
        other = Theory(skipped=self.skipped, classes=self.classes, individuals=self.individuals,
                       properties=self.properties, labels=self.labels,
                       definitions=self.definitions, source=self.source)
        for axiom in self.axioms:
            other.add(axiom.kind, *axiom.args)
        for axiom in axioms:
            other.add(axiom.kind, *axiom.args)
        return other

    def _sort(self):
        """A fixed order, so that the same ontology always writes the same proofs."""
        self.axioms.sort(key=lambda a: (a.kind, a.args))
        self.index.clear()
        for axiom in self.axioms:
            self.index[axiom.kind].append(axiom)

    def label(self, iri):
        return self.labels.get(iri) or _words(local(iri))

    def coverage(self):
        skipped = sum(self.skipped.values())
        total = self.translated + skipped
        return self.translated / total if total else 1.0


def local(iri):
    return str(iri).rsplit("#", 1)[-1].rsplit("/", 1)[-1] or str(iri)


def _words(name):
    return re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", name).replace("_", " ").strip()


def load(*paths, alignments=()):
    """Read ontology and data files into a Theory.

    A correspondence of an OAEI alignment is read as an equivalence between classes.
    That is the strong reading of "=", and a clash under it may be the alignment's fault.
    """
    graph = Graph()
    for path in paths:
        try:
            graph.parse(path)
        except Exception:
            graph.parse(path, format="xml")
    for path in alignments:
        for one, other in correspondences(path):
            graph.add((URIRef(one), OWL.equivalentClass, URIRef(other)))
    names = [str(p) for p in paths] + [f"alignment {p}" for p in alignments]
    return from_graph(graph, source=", ".join(names))


def correspondences(path):
    """The "=" pairs of an OAEI alignment in RDF."""
    with open(path, errors="ignore") as handle:
        text = handle.read()
    pairs = []
    for cell in re.findall(r"<(?:\w+:)?Cell[^>]*>(.*?)</(?:\w+:)?Cell>", text, flags=re.S):
        one = re.search(r'entity1[^>]*resource="([^"]+)"', cell)
        other = re.search(r'entity2[^>]*resource="([^"]+)"', cell)
        relation = re.search(r"relation[^>]*>([^<]*)<", cell)
        if one and other and (not relation or relation.group(1).strip() == "="):
            pairs.append((one.group(1), other.group(1)))
    return pairs


def from_graph(graph, source=""):
    theory = Theory(source=source)
    object_props = set(graph.subjects(RDF.type, OWL.ObjectProperty))
    data_props = set(graph.subjects(RDF.type, OWL.DatatypeProperty))
    annotation_props = set(graph.subjects(RDF.type, OWL.AnnotationProperty))
    theory.classes = {c for c in graph.subjects(RDF.type, OWL.Class) if isinstance(c, URIRef)}
    theory.classes = {str(c) for c in theory.classes}
    theory.properties = {str(p) for p in object_props if isinstance(p, URIRef)}
    for iri in theory.classes | theory.properties:
        term = URIRef(iri)
        label = graph.value(term, RDFS.label) or graph.value(term, SKOS_LABEL)
        if label is not None:
            theory.labels[iri] = str(label)
        elif local(iri) in OBO_RELATIONS:
            theory.labels[iri] = OBO_RELATIONS[local(iri)]
        for source in DEFINITIONS:
            found = sorted(str(o) for o in graph.objects(term, source))
            if found:
                theory.definitions[iri] = found[0]
                break

    for s, o in graph.subject_objects(RDFS.subClassOf):
        if isinstance(s, URIRef):
            _superclass(theory, graph, s, o)
    for s, o in graph.subject_objects(OWL.equivalentClass):
        if isinstance(s, URIRef):
            _superclass(theory, graph, s, o)
            if isinstance(o, URIRef):
                _superclass(theory, graph, o, s)
            else:  # the reverse, C ⊒ (complex), is a rule this fragment cannot state
                theory.skipped["equivalentClass, complex to named"] += 1
    for s, o in graph.subject_objects(OWL.disjointWith):
        if isinstance(s, URIRef) and isinstance(o, URIRef):
            theory.add("disjoint", s, o)
        else:
            theory.skipped["disjointWith on a complex class"] += 1
    for node in graph.subjects(RDF.type, OWL.AllDisjointClasses):
        members = _list(graph, graph.value(node, OWL.members))
        named = [m for m in members if isinstance(m, URIRef)]
        for i, one in enumerate(named):
            for other in named[i + 1:]:
                theory.add("disjoint", one, other)

    for s, o in graph.subject_objects(RDFS.domain):
        if not isinstance(s, URIRef) or s in annotation_props:
            continue
        if s in data_props:
            theory.skipped["domain of a datatype property"] += 1
            continue
        _on_property(theory, "domain", s, o)
    for s, o in graph.subject_objects(RDFS.range):
        if not isinstance(s, URIRef) or s in annotation_props:
            continue
        if (s in data_props or str(o).startswith(str(RDFS))
                or str(o).startswith("http://www.w3.org/2001/XMLSchema#")):
            theory.skipped["datatype range"] += 1
            continue
        _on_property(theory, "range", s, o)
    for s, o in graph.subject_objects(RDFS.subPropertyOf):
        if isinstance(s, URIRef) and isinstance(o, URIRef) and s not in data_props:
            theory.add("subprop", s, o)
    for s, o in graph.subject_objects(OWL.inverseOf):
        if isinstance(s, URIRef) and isinstance(o, URIRef):
            theory.add("inverse", s, o)
            theory.add("inverse", o, s)
    for s in graph.subjects(RDF.type, OWL.SymmetricProperty):
        theory.add("symmetric", s)
    for s in graph.subjects(RDF.type, OWL.TransitiveProperty):
        theory.add("transitive", s)
    for kind in (OWL.FunctionalProperty, OWL.InverseFunctionalProperty, OWL.AsymmetricProperty,
                 OWL.IrreflexiveProperty):
        count = sum(1 for _ in graph.subjects(RDF.type, kind))
        if count:
            theory.skipped[local(kind)] += count

    # An untyped individual is still a named thing: assertions on it count.
    known_terms = _vocabulary(graph)
    for s, o in graph.subject_objects(RDF.type):
        if not isinstance(s, URIRef) or o in _SKIP_TYPES or s in known_terms:
            continue
        if str(o).startswith(str(OWL)) or str(o).startswith(str(RDFS)):
            continue
        if isinstance(o, URIRef):
            theory.add("type", s, o)
            theory.individuals.add(str(s))
        else:
            theory.skipped["type assertion on a complex class"] += 1
    for s, p, o in graph:
        if isinstance(o, Literal) and isinstance(s, URIRef) and p in data_props:
            theory.skipped["literal value of a datatype property"] += 1
        if p == RDF.type or not isinstance(s, URIRef) or not isinstance(o, URIRef):
            continue
        if s in known_terms or o in known_terms or str(p).startswith(
                (str(RDF), str(RDFS), str(OWL))) or p in annotation_props or p in data_props:
            continue
        if p in object_props or not object_props:
            theory.add("rel", s, p, o)
            theory.individuals.update((str(s), str(o)))
    theory.skipped["sameAs or differentFrom"] += (
        sum(1 for _ in graph.subject_objects(OWL.sameAs))
        + sum(1 for _ in graph.subject_objects(OWL.differentFrom)))
    if not theory.skipped["sameAs or differentFrom"]:
        del theory.skipped["sameAs or differentFrom"]
    theory._sort()
    return theory


def _superclass(theory, graph, sub, sup):
    """sub ⊑ sup, for the shapes of sup that this fragment can state."""
    if sup == OWL.Thing:
        return
    if sup == OWL.Nothing:
        theory.add("nothing", sub)
    elif isinstance(sup, URIRef):
        theory.add("sub", sub, sup)
    elif (sup, RDF.type, OWL.Restriction) in graph:
        prop = graph.value(sup, OWL.onProperty)
        some, every = graph.value(sup, OWL.someValuesFrom), graph.value(sup, OWL.allValuesFrom)
        if isinstance(prop, URIRef) and isinstance(some, URIRef):
            if str(some).startswith("http://www.w3.org/2001/XMLSchema#"):
                theory.skipped["restriction to a datatype"] += 1
            else:
                theory.add("some", sub, prop, some)
        elif isinstance(prop, URIRef) and isinstance(every, URIRef):
            if str(every).startswith("http://www.w3.org/2001/XMLSchema#"):
                theory.skipped["restriction to a datatype"] += 1
            else:
                theory.add("all", sub, prop, every)
        elif some is not None or every is not None:
            theory.skipped["restriction with a complex filler"] += 1
        else:
            theory.skipped["cardinality or hasValue restriction"] += 1
    elif graph.value(sup, OWL.intersectionOf) is not None:
        for part in _list(graph, graph.value(sup, OWL.intersectionOf)):
            _superclass(theory, graph, sub, part)
    elif graph.value(sup, OWL.unionOf) is not None:
        theory.skipped["unionOf"] += 1
    elif graph.value(sup, OWL.complementOf) is not None:
        other = graph.value(sup, OWL.complementOf)
        if isinstance(other, URIRef):
            theory.add("disjoint", sub, other)
        else:
            theory.skipped["complementOf a complex class"] += 1
    else:
        theory.skipped["other class expression"] += 1


def _on_property(theory, kind, prop, cls):
    if cls == OWL.Thing:
        return
    if isinstance(cls, URIRef):
        theory.add(kind, prop, cls)
    else:
        theory.skipped[f"{kind} on a complex class"] += 1


def _list(graph, head):
    if head is None:
        return []
    try:
        return list(Collection(graph, head))
    except Exception:
        return []


def _vocabulary(graph):
    """IRIs that name classes or properties, which are not individuals here."""
    terms = set()
    for kind in (OWL.Class, RDFS.Class, OWL.ObjectProperty, OWL.DatatypeProperty,
                 OWL.AnnotationProperty, RDF.Property, OWL.Ontology, OWL.TransitiveProperty,
                 OWL.SymmetricProperty, OWL.FunctionalProperty, OWL.InverseFunctionalProperty):
        terms.update(graph.subjects(RDF.type, kind))
    for prop in (RDFS.subClassOf, OWL.equivalentClass, OWL.disjointWith):
        for s, o in graph.subject_objects(prop):
            terms.update((s, o))
    for prop in (RDFS.domain, RDFS.range, RDFS.subPropertyOf, OWL.inverseOf):
        terms.update(graph.subjects(prop))
    return {t for t in terms if isinstance(t, (URIRef, BNode, Literal))}
