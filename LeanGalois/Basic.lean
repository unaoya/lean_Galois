def Set (α : Type) := α → Prop

def Emptyset {α : Type} : Set α := fun _ => False

notation "∅" => Emptyset

notation "⊥" => Emptyset

def Univset {α : Type} : Set α := fun _ => True

notation "⊤" => Univset

def Set.Union {α : Type} (s t : Set α) : Set α :=
  fun a => s a ∨ t a

notation s " ∪ " t => Set.Union s t

def Set.Member {α : Type} (a : α) (s : Set α) : Prop := s a

notation a " ∈ " s => Set.Member a s

def Set.Disjoint {α : Type} (s t : Set α) : Prop :=
  ∀ a, ¬(s a ∧ t a)

def Set.Intersection {α : Type} (s t : Set α) : Set α :=
  fun a => s a ∧ t a

notation s " ∩ " t => Set.Intersection s t

def Family (α ι : Type) := ι → Set α

def Family.BigUnion {α ι : Type} (f : Family α ι) : Set α :=
  fun a => ∃ t : ι, a ∈ f t

-- 部分集合族が互いに素であること
def Family.Disjoint {α ι : Type} (f : Family α ι) : Prop := ∀ i j : ι, i ≠ j → Set.Disjoint (f i) (f j)

def Family.Covering {α ι : Type} (f : Family α ι) : Prop := f.BigUnion = ⊤

-- 部分集合族が分割であることの定義
-- def Decomposition {α ι : Type} (f : Family α ι) : Prop := (∀ i : ι, f i ≠ ∅) ∧ f.Covering ∧ f.Disjoint
structure Famiily.Decomposition {α ι : Type} (f : Family α ι) : Prop where
  nonempty : ∀ i : ι, f i ≠ ∅
  covering : f.Covering
  disjoint : f.Disjoint

-- 群の定義
-- 環のことも考えて演算と単位元を分けた方がいいかもしれない
class Group (G : Type) where
  mul : G → G → G
  inv : G → G
  one : G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  mul_left_inv : ∀ a : G, mul (inv a) a = one
  mul_right_inv : ∀ a : G, mul a (inv a) = one

theorem one_unique (G : Type) [Group G] (x : G) (h₁ : ∀ y : G, Group.mul x y = y) (h₂ : ∀ y : G, Group.mul y x = y) : x = Group.one := by
  calc
    x = Group.mul x Group.one := by rw [Group.mul_one x]
    _ = Group.one := by rw [h₁ Group.one]

theorem mul_one_inv (G : Type) [Group G] (x y : G) (h : Group.mul x y = Group.one) : y = Group.inv x := by
  have := congrArg (fun z => Group.mul (Group.inv x) z) h
  simp at this
  rw [Group.mul_one, ← Group.mul_assoc, Group.mul_left_inv, Group.one_mul] at this
  exact this

theorem inv_one_one (G : Type) [Group G] : (Group.one : G) = Group.inv Group.one := by
  apply mul_one_inv
  rw [Group.one_mul]

structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  one_mem : Group.one ∈ carrier
  mul_mem : ∀ {x y}, (x ∈ carrier) → (y ∈ carrier) → Group.mul x y ∈ carrier
  inv_mem : ∀ {x}, (x ∈ carrier) → (Group.inv x ∈ carrier)

-- 自明な部分群
def trivial_subgroup (G : Type) [Group G] : Subgroup G where
  carrier := Univset
  one_mem := trivial
  mul_mem := fun _ _ => trivial
  inv_mem := fun _ => trivial

def trivial_subgroup' (G : Type) [Group G] : Subgroup G where
  carrier := fun x => x = Group.one
  one_mem := rfl
  mul_mem := by
    intro x y hx hy
    rw [Set.Member] at *
    rw [hx, hy, Group.one_mul]
  inv_mem := by
    intro x hx
    rw [Set.Member] at *
    rw [hx]
    exact (inv_one_one G).symm

-- theorem Set.union_assoc {α : Type} (s t u : Set α) : ((s ∪ t) ∪ u) = (s ∪ (t ∪ u)) := by
--   funext x
--   ext
--   exact or_assoc

-- theorem Disjoint_iff_Intersect_empty {α : Type} (s t : Set α) : Set.Disjoint s t ↔ (Set.Intersection s t) = (∅ : Set α) := by
--   constructor
--   · intro h
--     funext x
--     ext
--     constructor
--     · intro h'
--       rw [Set.Empty]
--       rw [Set.Intersection] at h'
--       rw [Set.Disjoint] at h
--       exact h x h'
--     · intro h'
--       rw [Set.Empty] at h'
--       apply False.elim
--       exact h'
--   · intro h
--     rw [Set.Disjoint]
--     intro a
--     intro h'
--     have : s.Intersection t a = False := congrFun h a
--     rw [Set.Intersection] at this
--     rw [this] at h'
--     exact h'

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
