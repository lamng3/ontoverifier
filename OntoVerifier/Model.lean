/-!
# What an ontology means, and a checked way to refute a claim about it

An axiom is data, and `Axiom.holds` says what it means in an interpretation. This is
the one place the meaning of the translated fragment of OWL is defined.

`Entails T a` is the open-world reading: `a` holds in every interpretation that
satisfies `T`. To refute it, one interpretation is enough. `check` decides on a finite
model whether an axiom holds, and `check_iff` proves that it answers correctly, so a
model written by an untrusted program can be trusted once the kernel has run `check`.
-/

namespace OntoVerifier

structure Interp (U : Type) where
  cls : Nat → U → Prop
  rel : Nat → U → U → Prop
  ind : Nat → U

inductive Axiom where
  | sub (a b : Nat)
  | disjoint (a b : Nat)
  | nothing (a : Nat)
  | domain (p c : Nat)
  | range (p c : Nat)
  | subprop (p q : Nat)
  | inverse (p q : Nat)
  | symmetric (p : Nat)
  | transitive (p : Nat)
  | some (a p b : Nat)
  | all (a p b : Nat)
  | type (i c : Nat)
  | rel (i p j : Nat)

def Axiom.holds {U : Type} (I : Interp U) : Axiom → Prop
  | .sub a b => ∀ x, I.cls a x → I.cls b x
  | .disjoint a b => ∀ x, I.cls a x → I.cls b x → False
  | .nothing a => ∀ x, I.cls a x → False
  | .domain p c => ∀ x y, I.rel p x y → I.cls c x
  | .range p c => ∀ x y, I.rel p x y → I.cls c y
  | .subprop p q => ∀ x y, I.rel p x y → I.rel q x y
  | .inverse p q => ∀ x y, I.rel p x y → I.rel q y x
  | .symmetric p => ∀ x y, I.rel p x y → I.rel p y x
  | .transitive p => ∀ x y z, I.rel p x y → I.rel p y z → I.rel p x z
  | .some a p b => ∀ x, I.cls a x → ∃ y, I.rel p x y ∧ I.cls b y
  | .all a p b => ∀ x y, I.cls a x → I.rel p x y → I.cls b y
  | .type i c => I.cls c (I.ind i)
  | .rel i p j => I.rel p (I.ind i) (I.ind j)

/-- `I` satisfies every axiom of `T`. -/
def Models {U : Type} (I : Interp U) (T : List Axiom) : Prop :=
  ∀ a ∈ T, a.holds I

/-- `a` holds in every interpretation that satisfies `T`. -/
def Entails (T : List Axiom) (a : Axiom) : Prop :=
  ∀ (U : Type) (I : Interp U), Models I T → a.holds I

/-- A finite model: the (class, element) and (property, from, to) pairs that hold.
    The universe is `Nat`, and an individual named `i` is the element `i`. -/
structure FinModel where
  cls : List (Nat × Nat)
  rel : List (Nat × Nat × Nat)

def FinModel.interp (m : FinModel) : Interp Nat where
  cls c x := (c, x) ∈ m.cls
  rel p x y := (p, x, y) ∈ m.rel
  ind i := i

def FinModel.isCls (m : FinModel) (c x : Nat) : Bool := m.cls.contains (c, x)
def FinModel.isRel (m : FinModel) (p x y : Nat) : Bool := m.rel.contains (p, x, y)

theorem FinModel.isCls_iff (m : FinModel) (c x : Nat) :
    m.isCls c x = true ↔ (c, x) ∈ m.cls := by
  simp [FinModel.isCls]

theorem FinModel.isRel_iff (m : FinModel) (p x y : Nat) :
    m.isRel p x y = true ↔ (p, x, y) ∈ m.rel := by
  simp [FinModel.isRel]

/-- Every class-membership pair of class `a` passes `f`. -/
def FinModel.allCls (m : FinModel) (a : Nat) (f : Nat → Bool) : Bool :=
  m.cls.all fun e => e.1 != a || f e.2

/-- Every edge of property `p` passes `f`. -/
def FinModel.allRel (m : FinModel) (p : Nat) (f : Nat → Nat → Bool) : Bool :=
  m.rel.all fun e => e.1 != p || f e.2.1 e.2.2

theorem FinModel.allCls_iff (m : FinModel) (a : Nat) (f : Nat → Bool) :
    m.allCls a f = true ↔ ∀ x, (a, x) ∈ m.cls → f x = true := by
  simp only [FinModel.allCls, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · intro h x hx
    rcases h _ hx with h' | h'
    · exact absurd rfl h'
    · exact h'
  · intro h e he
    by_cases hc : e.1 = a
    · refine Or.inr (h e.2 ?_)
      have : (a, e.2) = e := by cases e; simp_all
      rw [this]; exact he
    · exact Or.inl hc

theorem FinModel.allRel_iff (m : FinModel) (p : Nat) (f : Nat → Nat → Bool) :
    m.allRel p f = true ↔ ∀ x y, (p, x, y) ∈ m.rel → f x y = true := by
  simp only [FinModel.allRel, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · intro h x y hx
    rcases h _ hx with h' | h'
    · exact absurd rfl h'
    · exact h'
  · intro h e he
    by_cases hc : e.1 = p
    · refine Or.inr (h e.2.1 e.2.2 ?_)
      have : (p, e.2.1, e.2.2) = e := by
        obtain ⟨a, b, c⟩ := e
        simp_all
      rw [this]; exact he
    · exact Or.inl hc

/-- Does the axiom hold on this finite model? -/
def check (m : FinModel) : Axiom → Bool
  | .sub a b => m.allCls a fun x => m.isCls b x
  | .disjoint a b => m.allCls a fun x => !m.isCls b x
  | .nothing a => m.allCls a fun _ => false
  | .domain p c => m.allRel p fun x _ => m.isCls c x
  | .range p c => m.allRel p fun _ y => m.isCls c y
  | .subprop p q => m.allRel p fun x y => m.isRel q x y
  | .inverse p q => m.allRel p fun x y => m.isRel q y x
  | .symmetric p => m.allRel p fun x y => m.isRel p y x
  | .transitive p => m.allRel p fun x y => m.allRel p fun y' z => y' != y || m.isRel p x z
  | .some a p b => m.allCls a fun x => m.rel.any fun e => e.1 == p && e.2.1 == x && m.isCls b e.2.2
  | .all a p b => m.allCls a fun x => m.allRel p fun s y => s != x || m.isCls b y
  | .type i c => m.isCls c i
  | .rel i p j => m.isRel p i j

/-- `check` says exactly what `holds` means. This is what makes an untrusted model safe. -/
theorem check_iff (m : FinModel) (a : Axiom) : check m a = true ↔ a.holds m.interp := by
  cases a with
  | sub a b =>
    simp only [check, FinModel.allCls_iff, FinModel.isCls_iff, Axiom.holds, FinModel.interp]
  | disjoint a b =>
    simp only [check, FinModel.allCls_iff, Axiom.holds, FinModel.interp]
    constructor
    · intro h x ha hb
      have := h x ha
      simp [(FinModel.isCls_iff m b x).mpr hb] at this
    · intro h x ha
      cases hb : m.isCls b x with
      | false => rfl
      | true => exact (h x ha ((FinModel.isCls_iff m b x).mp hb)).elim
  | nothing a =>
    simp only [check, FinModel.allCls_iff, Axiom.holds, FinModel.interp]
    constructor
    · intro h x ha
      simpa using h x ha
    · intro h x ha
      exact (h x ha).elim
  | domain p c =>
    simp only [check, FinModel.allRel_iff, FinModel.isCls_iff, Axiom.holds, FinModel.interp]
  | range p c =>
    simp only [check, FinModel.allRel_iff, FinModel.isCls_iff, Axiom.holds, FinModel.interp]
  | subprop p q =>
    simp only [check, FinModel.allRel_iff, FinModel.isRel_iff, Axiom.holds, FinModel.interp]
  | inverse p q =>
    simp only [check, FinModel.allRel_iff, FinModel.isRel_iff, Axiom.holds, FinModel.interp]
  | symmetric p =>
    simp only [check, FinModel.allRel_iff, FinModel.isRel_iff, Axiom.holds, FinModel.interp]
  | transitive p =>
    simp only [check, FinModel.allRel_iff, Axiom.holds, FinModel.interp, Bool.or_eq_true,
      bne_iff_ne, ne_eq, FinModel.isRel_iff]
    constructor
    · intro h x y z hxy hyz
      rcases h x y hxy y z hyz with h' | h'
      · exact absurd rfl h'
      · exact h'
    · intro h x y hxy y' z hyz
      by_cases he : y' = y
      · subst he
        exact Or.inr (h x y' z hxy hyz)
      · exact Or.inl he
  | some a p b =>
    simp only [check, FinModel.allCls_iff, Axiom.holds, FinModel.interp, List.any_eq_true,
      Bool.and_eq_true, beq_iff_eq, FinModel.isCls_iff]
    constructor
    · intro h x ha
      obtain ⟨⟨q, s, y⟩, he, ⟨hq, hs⟩, hc⟩ := h x ha
      simp only at hq hs hc
      subst hq hs
      exact ⟨y, he, hc⟩
    · intro h x ha
      obtain ⟨y, he, hc⟩ := h x ha
      exact ⟨(p, x, y), he, ⟨rfl, rfl⟩, hc⟩
  | all a p b =>
    simp only [check, FinModel.allCls_iff, FinModel.allRel_iff, Axiom.holds, FinModel.interp,
      Bool.or_eq_true, bne_iff_ne, ne_eq, FinModel.isCls_iff]
    constructor
    · intro h x y ha hr
      rcases h x ha x y hr with h' | h'
      · exact absurd rfl h'
      · exact h'
    · intro h x ha s y hr
      by_cases he : s = x
      · subst he
        exact Or.inr (h s y ha hr)
      · exact Or.inl he
  | type i c =>
    simp only [check, FinModel.isCls_iff, Axiom.holds, FinModel.interp]
  | rel i p j =>
    simp only [check, FinModel.isRel_iff, Axiom.holds, FinModel.interp]

/-! ## Checking a large theory

Most axioms of a large ontology say nothing about a small model: `A ⊑ B` holds at once if
no element is in `A`. Scanning the model to find that out, for every axiom, costs the kernel
minutes. So a model comes with a mask, a number with one bit for each term it uses. The
kernel first checks that the mask covers the model, and can then skip an axiom whose premise
bit is off using only its native arithmetic on numbers. `verified_sound` proves the shortcut
changes nothing, and a wrong mask only makes the check fail. -/

/-- Bit `s` of the mask. Its arithmetic properties do not matter to the proof. -/
def bit (mask s : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight mask s) 1) 1

/-- The term whose absence from a model makes the axiom hold, if there is one. -/
def Axiom.premise : Axiom → Option Nat
  | .sub a _ | .disjoint a _ | .nothing a | .some a _ _ | .all a _ _ => .some a
  | .domain p _ | .range p _ | .subprop p _ | .inverse p _ | .symmetric p | .transitive p =>
    .some p
  | .type .. | .rel .. => .none

/-- The mask has a bit for every class and property the model uses. -/
def FinModel.covered (m : FinModel) (mask : Nat) : Bool :=
  m.cls.all (fun e => bit mask e.1) && m.rel.all (fun e => bit mask e.1)

/-- `check`, skipping an axiom whose premise is not in the mask. -/
def quick (m : FinModel) (mask : Nat) (a : Axiom) : Bool :=
  match a.premise with
  | .some s => !bit mask s || check m a
  | .none => check m a

def FinModel.verified (m : FinModel) (mask : Nat) (T : List Axiom) : Bool :=
  m.covered mask && T.all (quick m mask)

/-- With a covering mask, an axiom whose premise is absent passes `check` regardless. -/
theorem check_of_absent {m : FinModel} {mask : Nat} {a : Axiom} {s : Nat}
    (hc : m.covered mask = true) (hp : a.premise = .some s) (hs : bit mask s = false) :
    check m a = true := by
  simp only [FinModel.covered, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hcls, hrel⟩ := hc
  have noCls : ∀ x, (s, x) ∉ m.cls := fun x hx => by
    have := hcls _ hx
    simp_all
  have noRel : ∀ x y, (s, x, y) ∉ m.rel := fun x y hx => by
    have := hrel _ hx
    simp_all
  cases a <;> simp only [Axiom.premise, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp only [check] <;>
    first
      | exact (FinModel.allCls_iff m _ _).mpr fun x hx => absurd hx (noCls x)
      | exact (FinModel.allRel_iff m _ _).mpr fun x y hx => absurd hx (noRel x y)

theorem check_of_quick {m : FinModel} {mask : Nat} {a : Axiom}
    (hc : m.covered mask = true) (h : quick m mask a = true) : check m a = true := by
  unfold quick at h
  cases hp : a.premise with
  | none => simpa [hp] using h
  | some s =>
    cases hs : bit mask s with
    | false => exact check_of_absent hc hp hs
    | true => simpa [hp, hs] using h

/-- The check with the shortcut says the same as the check without it. -/
theorem verified_sound {m : FinModel} {mask : Nat} {T : List Axiom}
    (h : m.verified mask T = true) : Models m.interp T := by
  simp only [FinModel.verified, Bool.and_eq_true] at h
  intro a ha
  exact (check_iff m a).mp (check_of_quick h.1 (List.all_eq_true.mp h.2 a ha))

/-- A model of `T` where the axiom fails refutes the entailment. -/
theorem refutes {T : List Axiom} {a : Axiom} (m : FinModel) (mask : Nat)
    (hT : m.verified mask T = true) (ha : check m a = false) : ¬ Entails T a := by
  intro h
  have holds := h Nat m.interp (verified_sound hT)
  have := (check_iff m a).mpr holds
  simp [ha] at this

/-- A model of `T` with an element of class `c`: the class can have instances. -/
theorem satisfiable {T : List Axiom} {c : Nat} (m : FinModel) (mask x : Nat)
    (hT : m.verified mask T = true) (hc : m.isCls c x = true) :
    ∃ (U : Type) (I : Interp U), Models I T ∧ ∃ y, I.cls c y :=
  ⟨Nat, m.interp, verified_sound hT, x, (FinModel.isCls_iff m c x).mp hc⟩

/-- A model of `T`: the ontology, with its data, is consistent. -/
theorem consistent {T : List Axiom} (m : FinModel) (mask : Nat)
    (hT : m.verified mask T = true) :
    ∃ (U : Type) (I : Interp U), Models I T :=
  ⟨Nat, m.interp, verified_sound hT⟩

end OntoVerifier
