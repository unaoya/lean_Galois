import LeanGalois.Set

def Family (α ι : Type) := ι → Set α

namespace Family

def BigUnion {α ι : Type} (f : Family α ι) : Set α :=
  fun a => ∃ t : ι, a ∈ f t

-- 部分集合族が互いに素であること
def Disjoint {α ι : Type} (f : Family α ι) : Prop := ∀ i j : ι, i ≠ j → Set.Disjoint (f i) (f j)

def Covering {α ι : Type} (f : Family α ι) : Prop := f.BigUnion = ⊤

-- 部分集合族が分割であることの定義
-- def Decomposition {α ι : Type} (f : Family α ι) : Prop := (∀ i : ι, f i ≠ ∅) ∧ f.Covering ∧ f.Disjoint
structure Decomposition {α ι : Type} (f : Family α ι) : Prop where
  nonempty : ∀ i : ι, f i ≠ ∅
  covering : f.Covering
  disjoint : f.Disjoint

end Family

variable {α : Type} (r : α → α → Prop) (h : Equivalence r)

--def s : Setoid α := ⟨r, h⟩

def equivrel_to_family : Family α (Quotient ⟨r, h⟩) := by
  apply Quotient.lift (fun x => (fun y => r x y))
  intro x y h'
  funext z
  ext
  exact ⟨fun h'' => h.trans (h.symm h') h'', fun h'' => h.trans h' h''⟩

theorem equivrel_to_decomp : (equivrel_to_family r h).Decomposition := by
  have h₁ (x : α) : r x x := h.refl x
  have h₂ (x : α) : equivrel_to_family r h (Quot.mk r x) = (fun x => (fun y => r x y)) x := rfl
  have h₃ (x : α) : Quot.mk r x = Quot.mk (@Setoid.r α ⟨r, h⟩) x := rfl
  constructor
  · rintro ⟨x⟩
    intro h'
    rw [← h₃, h₂] at h'
    simp at h'
    have := congrFun h' x
    simp at this
    exact this.1 (h₁ x)
  · funext x
    simp
    constructor
    · intro _
      rw [Univset]
      exact trivial
    · intro _
      rw [Family.BigUnion]
      have : x ∈ equivrel_to_family r h (Quot.mk r x) := by
        rw [h₂]
        simp
        exact h.refl x
      exact ⟨Quot.mk r x, this⟩
  · rintro i j h'
    rw [Set.Disjoint]
    intro x
    intro h''
    apply h'
    rcases Quotient.exists_rep i with ⟨a, ha⟩
    rcases Quotient.exists_rep j with ⟨b, hb⟩
    rw [← ha, ← hb]
    apply Quotient.sound
    have h₁ : equivrel_to_family r h (Quotient.mk ⟨r, h⟩ a) = (fun x => (fun y => r x y)) a := rfl
    rw [ha] at h₁
    have h₂ : equivrel_to_family r h (Quotient.mk ⟨r, h⟩ b) = (fun x => (fun y => r x y)) b := rfl
    rw [hb] at h₂
    rw [h₁, h₂] at h''
    simp at h''
    exact h.trans h''.1 (h.symm h''.2)
