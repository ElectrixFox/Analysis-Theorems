import Mathlib

class Mgroup (G : Type) extends Mul G, One G, Inv G where
mul_assoc (a b c : G) : (a * b) * c = a * (b * c)
one_mul (a : G) : 1 * a = a
mul_one (a : G) : a * 1 = a
mul_left_inv (a : G) : a⁻¹ * a = 1
mul_right_inv (a : G) : a * a⁻¹ = 1

def abelian (G : Type) [Mgroup G] : Prop := ∀ (x : G) (y : G), x * y = y * x

lemma grp_unique_id (G : Type) [Mgroup G] (e1 e2 : G) (he1 : ∀ (x : G), e1 * x = x ∧ x = x * e1) (he2 : ∀ (x : G), e2 * x = x ∧ x = x * e2) : e1 = e2 := by
  specialize he1 e2
  specialize he2 e1
  rw [←he1.right, ←he2.right] at he1
  apply he1.left
