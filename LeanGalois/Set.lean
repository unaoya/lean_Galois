def Set (α : Type) := α → Prop

def Emptyset {α : Type} : Set α := fun _ => False

notation "∅" => Emptyset

notation "⊥" => Emptyset

def Univset {α : Type} : Set α := fun _ => True

notation "⊤" => Univset

namespace Set

def Union {α : Type} (s t : Set α) : Set α :=
  fun a => s a ∨ t a

notation s " ∪ " t => Union s t

def Member {α : Type} (a : α) (s : Set α) : Prop := s a

notation a " ∈ " s => Member a s

def Disjoint {α : Type} (s t : Set α) : Prop :=
  ∀ a, ¬(s a ∧ t a)

def Intersection {α : Type} (s t : Set α) : Set α :=
  fun a => s a ∧ t a

notation s " ∩ " t => Intersection s t

theorem union_assoc {α : Type} (s t u : Set α) : ((s ∪ t) ∪ u) = (s ∪ (t ∪ u)) := by
  funext x
  ext
  exact or_assoc

theorem Disjoint_iff_Intersect_empty {α : Type} (s t : Set α) : Set.Disjoint s t ↔ (Set.Intersection s t) = (∅ : Set α) := by
  constructor
  · intro h
    funext x
    ext
    exact ⟨fun h' => h x h', fun h' => False.elim h'⟩
  · intro h a h'
    have : s.Intersection t a = False := congrFun h a
    rw [← this]
    exact h'

end Set
