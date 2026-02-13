import CanonicalMin

def powerset_mono :
  (α : Type) →
  (Goal : Type) →
  (s : (a : α) → Type) → (t : (a : α) → Type) →
  (mono : (mp : (hst : (x : (a : α) → Type) → (hxs : (a : α) → (hx : x a) → s a) → (a : α) → (hx : x a) → t a) → (a : α) → (hs : s a) → t a) →
          (mpr : (hst : (a : α) → (hs : s a) → t a) → (x : (a : α) → Type) → (hxs : (a : α) → (hx : x a) → s a) → (a : α) → (hx : x a) → t a) → Goal) →
  Goal :=
  by canonical_min

def Cantor :
  (A : Type) →
  (Eq : (x : Type) → (y : Type) → Type) →
  (f : (a : A) → (b : A) → Type) →
  (f_inv : (q : (a : A) → Type) → A) →
  (f_surj : (q : (a : A) → Type) → (x : A) → Eq (f (f_inv q) x) (q x)) →
  (Not : (x : Type) → Type) →
  (Goal : Type) →
  (A_ne_Not_A : (A : Type) → (h : Eq A (Not A)) → Goal) →
  Goal := by
  canonical_min
