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
