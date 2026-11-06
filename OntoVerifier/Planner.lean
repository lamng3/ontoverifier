/-!
# When a selection may cross a join

A model of SPARQL solutions with unbound variables, enough to state the rules a
query planner uses to move FILTER around joins (Pérez et al., TODS 2009).

This proves things about the model, not about any planner's source code. What it
gives a planner is the exact side condition each rewrite needs, and a proof that
the condition cannot be dropped.
-/

namespace OntoVerifier.Planner

abbrev Var := Nat
abbrev Val := Nat

/-- A solution: each variable is bound to a value or unbound. -/
abbrev Sol := Var → Option Val

/-- Two solutions agree on every variable both of them bind. -/
def Compatible (a b : Sol) : Prop :=
  ∀ v, a v = none ∨ b v = none ∨ a v = b v

/-- The solution binding what either side binds. -/
def merge (a b : Sol) : Sol := fun v =>
  match a v with
  | some x => some x
  | none => b v

/-- Bags of solutions, as in SPARQL, with an order so that equality is plain list equality. -/
abbrev Bag := List Sol

/-- The natural join, for any decision procedure `compat` for compatibility. -/
def join (compat : Sol → Sol → Bool) (A B : Bag) : Bag :=
  A.flatMap fun a => (B.filter (compat a)).map (merge a)

/-- A filter only looks at the variables in `vs`, and reads an unbound one the same way
    in any two solutions that agree on `vs`. -/
def DependsOn (p : Sol → Bool) (vs : List Var) : Prop :=
  ∀ a b : Sol, (∀ v ∈ vs, a v = b v) → p a = p b

/-- Every solution of the bag binds every variable in `vs`: Hermes's `certain`. -/
def Certain (vs : List Var) (A : Bag) : Prop :=
  ∀ a ∈ A, ∀ v ∈ vs, (a v).isSome

/-- The relation `compat` really decides compatibility. -/
def Sound (compat : Sol → Sol → Bool) : Prop :=
  ∀ a b, compat a b = true → Compatible a b

theorem merge_left {a b : Sol} {v : Var} (h : (a v).isSome) : merge a b v = a v := by
  unfold merge
  cases hv : a v with
  | none => simp [hv] at h
  | some x => rfl

theorem merge_right {a b : Sol} {v : Var} (hc : Compatible a b) (h : (b v).isSome) :
    merge a b v = b v := by
  unfold merge
  cases ha : a v with
  | none => rfl
  | some x =>
    rcases hc v with h0 | h0 | h0
    · simp [ha] at h0
    · simp [h0] at h
    · simpa [ha] using h0

/-- Push a selection into the left of a join, when the left always binds its variables. -/
theorem filter_join_left (compat : Sol → Sol → Bool) (p : Sol → Bool) (vs : List Var)
    (A B : Bag) (dep : DependsOn p vs) (bound : Certain vs A) :
    (join compat A B).filter p = join compat (A.filter p) B := by
  induction A with
  | nil => rfl
  | cons a rest ih =>
    have hrest : Certain vs rest := fun x hx => bound x (List.mem_cons_of_mem a hx)
    have ha : ∀ v ∈ vs, (a v).isSome := bound a List.mem_cons_self
    have hsame : ∀ b : Sol, p (merge a b) = p a := fun b =>
      dep _ _ (fun v hv => merge_left (ha v hv))
    have hrec := ih hrest
    simp only [join, List.flatMap_cons, List.filter_append] at hrec ⊢
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, if_true, List.flatMap_cons]
      rw [hrec]
      congr 1
      rw [List.filter_eq_self]
      intro x hx
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
      rw [hsame b]; exact hp
    · simp only [List.filter_cons, hp, if_false]
      rw [hrec]
      have hnil : ((B.filter (compat a)).map (merge a)).filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
        rw [hsame b]; exact hp
      rw [hnil]; rfl

/-- One row of a join: a selection the right side always decides can run before the merge. -/
theorem filter_row (compat : Sol → Sol → Bool) (p : Sol → Bool) (vs : List Var) (a : Sol)
    (B : Bag) (sound : Sound compat) (dep : DependsOn p vs) (bound : Certain vs B) :
    ((B.filter (compat a)).map (merge a)).filter p
      = ((B.filter p).filter (compat a)).map (merge a) := by
  induction B with
  | nil => rfl
  | cons b more ih =>
    have hb : ∀ v ∈ vs, (b v).isSome := bound b List.mem_cons_self
    have hmore : Certain vs more := fun x hx => bound x (List.mem_cons_of_mem b hx)
    have hrec := ih hmore
    cases hc : compat a b with
    | true =>
      have hsame : p (merge a b) = p b :=
        dep _ _ (fun v hv => merge_right (sound a b hc) (hb v hv))
      cases hp : p b with
      | true => simp [List.filter_cons, hc, hp, hsame, hrec]
      | false => simp [List.filter_cons, hc, hp, hsame, hrec]
    | false =>
      cases hp : p b with
      | true => simp [List.filter_cons, hc, hp, hrec]
      | false => simp [List.filter_cons, hc, hp, hrec]

/-- Push a selection into the right of a join, when the right always binds its variables. -/
theorem filter_join_right (compat : Sol → Sol → Bool) (p : Sol → Bool) (vs : List Var)
    (A B : Bag) (sound : Sound compat) (dep : DependsOn p vs) (bound : Certain vs B) :
    (join compat A B).filter p = join compat A (B.filter p) := by
  induction A with
  | nil => rfl
  | cons a rest ih =>
    simp only [join, List.flatMap_cons, List.filter_append] at ih ⊢
    rw [ih, filter_row compat p vs a B sound dep bound]

/-- Selections distribute over union, with no side condition. -/
theorem filter_union (p : Sol → Bool) (A B : Bag) :
    (A ++ B).filter p = A.filter p ++ B.filter p :=
  List.filter_append ..

section Lifting

/-- The rewrite an optimizer does when it lifts a selection out of an inner group
    and places it above the join. It is sound under the same condition, read backwards:
    the group the selection came from must already bind what it reads. -/
theorem lift_sound (compat : Sol → Sol → Bool) (p : Sol → Bool) (vs : List Var)
    (A B : Bag) (dep : DependsOn p vs) (bound : Certain vs A) :
    join compat (A.filter p) B = (join compat A B).filter p :=
  (filter_join_left compat p vs A B dep bound).symm

/-! And the condition cannot be dropped. A one-variable counterexample: `x` is not bound
    in the group holding the filter, only in the one joined to it. -/

def x : Var := 0
def empty : Sol := fun _ => none
def withX : Sol := fun v => if v == x then some 5 else none

/-- `FILTER(?x > 1)`: an unbound `?x` is an error, which a filter treats as false. -/
def xAboveOne : Sol → Bool := fun s =>
  match s x with
  | some n => decide (1 < n)
  | none => false

/-- Everything is compatible here, since only one side ever binds `x`. -/
def always : Sol → Sol → Bool := fun _ _ => true

theorem depends_xAboveOne : DependsOn xAboveOne [x] := by
  intro a b h
  have : a x = b x := h x (by simp)
  simp [xAboveOne, this]

/-- `{ {} FILTER(?x > 1) } { ?x }` has no solutions: the inner filter cannot see `?x`. -/
theorem inner_filter_is_empty :
    (join always ([empty].filter xAboveOne) [withX]).length = 0 := by
  rfl

/-- With the filter above the join there is a solution. -/
theorem lifted_filter_is_not_empty :
    ((join always [empty] [withX]).filter xAboveOne).length = 1 := by
  rfl

/-- So lifting a selection past a join changes the answers when the selection's group
    does not bind what it reads. -/
theorem lift_unsound_without_scope :
    ¬ ∀ (compat : Sol → Sol → Bool) (p : Sol → Bool) (A B : Bag),
      join compat (A.filter p) B = (join compat A B).filter p := by
  intro h
  have key := h always xAboveOne [empty] [withX]
  have one := lifted_filter_is_not_empty
  rw [← key, inner_filter_is_empty] at one
  exact absurd one (by decide)

/-- The missing condition, in the shape the counterexample violates. -/
theorem counterexample_breaks_certain : ¬ Certain [x] [empty] := by
  intro h
  have := h empty (by simp) x (by simp)
  simp [empty] at this

end Lifting

end OntoVerifier.Planner
