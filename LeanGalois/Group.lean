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

namespace Group
variable {G : Type} [Group G] (x y : G)

theorem one_unique (h₁ : ∀ y : G, Group.mul x y = y) : x = one := by
  calc
    x = mul x one := by rw [mul_one x]
    _ = one := by rw [h₁ one]

theorem one_unique' (h₂ : ∀ y : G, Group.mul y x = y) : x = one := by
  calc
    x = mul one x := by rw [one_mul x]
    _ = one := by rw [h₂ one]

theorem mul_one_inv (h : mul x y = one) : y = inv x := by
  have := congrArg (fun z => mul (inv x) z) h
  simp at this
  rw [mul_one, ← mul_assoc, mul_left_inv, one_mul] at this
  exact this

theorem inv_one_one : (one : G) = inv one := by
  apply mul_one_inv
  rw [one_mul]

theorem mul_inv (g h : G) : inv (mul g h) = mul (inv h) (inv g) := by
  sorry

theorem inv_inv (g : G) : inv (inv g) = g := by
  sorry

end Group

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
    exact Group.inv_one_one.symm

class LGSet (G : Type) [Group G] (α : Type) where
  act : G → α → α
  act_one : ∀ a : α, act Group.one a = a
  act_mul : ∀ g h : G, ∀ a : α, act (Group.mul g h) a = act g (act h a)
  act_inv : ∀ g : G, ∀ a : α, act (Group.inv g) (act g a) = a

def isLFixedPoint (G : Type) [Group G] (α : Type) [LGSet G α] (a : α) : Prop :=
  ∀ g : G, LGSet.act g a = a

instance self_LGSet (G : Type) [Group G] : LGSet G G where
  act := fun g h ↦ Group.mul g h
  act_one := Group.one_mul
  act_mul := Group.mul_assoc
  act_inv := by
    intro g h
    simp
    rw [← Group.mul_assoc, Group.mul_left_inv, Group.one_mul]

instance fun_LGSet (G : Type) [Group G] (α : Type) [LGSet G α] (β : Type) : LGSet G (α → β) where
  act := fun g f ↦ fun a => f (LGSet.act (Group.inv g) a)
  act_one := by
    intro f
    funext a
    simp
    rw [← Group.inv_one_one, LGSet.act_one]
  act_mul := by
    intro g h f
    funext a
    simp
    rw [Group.mul_inv, LGSet.act_mul]
  act_inv := by
    intro g f
    funext a
    simp
    rw [Group.inv_inv, LGSet.act_inv]

instance PSet_LGSet {G : Type} [Group G] {α : Type} [LGSet G α] : LGSet G (Set α) := by
  rw [Set]
  exact (inferInstance : LGSet G (α → Prop))

theorem PSet_LGSet_eq_image {G : Type} [Group G] {α : Type} [LGSet G α] (A : Set α) (g : G) :
  LGSet.act g A = fun a => A (LGSet.act (Group.inv g) a) := by
  rfl
