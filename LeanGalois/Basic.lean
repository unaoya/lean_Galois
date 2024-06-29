def Set (α : Type) := α → Prop

def Set.Union {α : Type} (s t : Set α) : Set α :=
  fun a => s a ∨ t a

notation s " ∪ " t => Set.Union s t

def Set.Member {α : Type} (a : α) (s : Set α) : Prop := s a

notation a " ∈ " s => Set.Member a s

def Set.Family (α ι : Type) := ι → Set α

def Set.BigUnion {α ι : Type} (f : Set.Family α ι) : Set α :=
  fun a => ∃ t : ι, a ∈ f t

def Set.Disjoint {α : Type} (s t : Set α) : Prop :=
  ∀ a, ¬(s a ∧ t a)

def Set.Empty {α : Type} : Set α := fun _ => False

notation "∅" => Set.Empty

def Set.Intersect {α : Type} (s t : Set α) : Set α :=
  fun a => s a ∧ t a

-- 部分集合族が互いに素であること
def DisjointFamily {α ι : Type} (f : Set.Family α ι) : Prop := ∀ i j : ι, i ≠ j → Set.Disjoint (f i) (f j)

notation "⊥" => Set.Empty

def Set.Univ {α : Type} : Set α := fun _ => True

notation "⊤" => Set.Univ

def Covering {α ι : Type} (f : Set.Family α ι) : Prop := Set.BigUnion f = ⊤

-- 部分集合族が分割であることの定義
def Decomposition {α ι : Type} (f : Set.Family α ι) : Prop := (∀ i : ι, f i ≠ ∅) ∧ Covering f ∧ DisjointFamily f



theorem Set.union_assoc {α : Type} (s t u : Set α) : ((s ∪ t) ∪ u) = (s ∪ (t ∪ u)) := by
  funext x
  ext
  exact or_assoc

theorem Disjoint_iff_Intersect_empty {α : Type} (s t : Set α) : Set.Disjoint s t ↔ (Set.Intersect s t) = (∅ : Set α) := by
  constructor
  · intro h
    funext x
    ext
    constructor
    · intro h'
      rw [Set.Empty]
      rw [Set.Intersect] at h'
      rw [Set.Disjoint] at h
      exact h x h'
    · intro h'
      rw [Set.Empty] at h'
      apply False.elim
      exact h'
  · intro h
    rw [Set.Disjoint]
    intro a
    intro h'
    have : s.Intersect t a = False := congrFun h a
    rw [Set.Intersect] at this
    rw [this] at h'
    exact h'

-- def Set.Contained {α : Type} (s t : Set α) : Prop :=
--   ∀ a, s a → t a

-- instance : LE (Set α) := ⟨Set.Contained⟩

-- example {α : Type} (s t : Set α) : Set.Contained s t ↔ s ≤ t := by
--   rfl

-- -- LE の一般的な性質（そんなものはない）を使える
-- example {α : Type} (x : α) (s t : Set α) (h : Set.Contained s t) : Set.Member x s → Set.Member x t :=
--   h x

-- example {α : Type} (x : α) (s t : Set α) : Set.Member x (Set.Union s t) = (Set.Member x s ∨ Set.Member x t) :=
--   rfl


-- example {α : Type} (s t : Set α) : Set.Disjoint s t ↔ (Set.Intersect s t) = Set.Empty := by
--   constructor <;> intro h
--   · funext x
--     rw [Set.Intersect]
--     rw [Set.Disjoint] at h
--     rw [Set.Empty]
--     ext
--     constructor
--     · intro h'
--       exact h x h'
--     · intro h'
--       exact False.rec h'
--   · rw [Set.Disjoint]
--     intro x h'
--     have : s.Intersect t x = False := congrFun h x
--     rw [Set.Intersect] at this
--     rw [this] at h'
--     exact h'

-- inductive MyFalse : Prop

-- #check False.rec

-- -- LEとかEqとかのinstanceを作る？

-- -- 集合の分割を定義する。
-- -- 一般の部分集合の分割を作るか、αだけにするか？


-- -- 部分集合族の和が全体に一致すること

-- def Range (n : Nat) : Type := {i : Nat // i < n}

-- def F : Range 1 → Set Nat
--   | ⟨0, _⟩ => fun x => x = 0

-- def H : Range 3 → Set Nat
--   | ⟨0, _⟩ => fun x => x = 0
--   | ⟨1, _⟩ => fun x => x = 0
--   | ⟨2, _⟩ => fun x => x = 0

-- def G : Range 2 → Set Nat
--   | ⟨0, _⟩ => fun x => x = 0
--   | ⟨1, _⟩ => fun x => x ≠ 0

-- example : Decomposition G := by
--   constructor
--   · funext x
--     ext
--     rw [BigUnion]
--     rw [Set.Univ]
--     by_cases h : x = 0
--     · sorry
--     · sorry
--   · intro i j h
--     sorry
