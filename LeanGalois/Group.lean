import LeanGalois.Set

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

theorem one_unique (G : Type) [Group G] (x : G) (h₁ : ∀ y : G, Group.mul x y = y) : x = Group.one := by
  calc
    x = Group.mul x Group.one := by rw [Group.mul_one x]
    _ = Group.one := by rw [h₁ Group.one]

theorem one_unique' (G : Type) [Group G] (x : G) (h₂ : ∀ y : G, Group.mul y x = y) : x = Group.one := by
  calc
    x = Group.mul Group.one x := by rw [Group.one_mul x]
    _ = Group.one := by rw [h₂ Group.one]

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
