import CanonicalMin

def Iff_refl :
  (Iff : (α : Type) → (β : Type) → Type) →
  (Iff_mk : (α : Type) → (β : Type) → (mp : (a : α) → β) → (mpr : (b : β) → α) → Iff α β) →
  (α : Type) → Iff α α := by
  canonical_min

def Or_elim :
  (Or : (a : Type) → (b : Type) → Type) →
  (Or_inl : (a : Type) → (b : Type) → (l : a) → Or a b) →
  (Or_inr : (a : Type) → (b : Type) → (r : b) → Or a b) →
  (Or_rec : (a : Type) → (b : Type) → (motive : (h : Or a b) → Type) → (inl : (h : a) → motive (Or_inl a b h)) →
    (inr : (h : b) → motive (Or_inr a b h)) → (t : Or a b) → motive t) →
  (a : Type) → (b : Type) → (c : Type) → (hab : Or a b) → (hac : (x : a) → c) → (hbc : (x : b) → c) → c := by
  canonical_min

def False_elim :
  (False : Type) →
  (False_rec : (motive : (h : False) → Type) → (t : False) → motive t) →
  (C : Type) → (h : False) → C := by
  canonical_min

def peirce :
  (False : Type) →
  (contr : (p : Type) → (nnp : (np : (h : p) → False) → False) → p) →
  (a : Type) → (b : Type) → (aba : (ab : (h : a) → b) → a) → a := by
  canonical_min

def PUnit_ext :
  (Eq : (α : Type) → (x : α) → (y : α) → Type) →
  (Eq_refl : (α : Type) → (x : α) → Eq α x x) →
  (Eq_rec : (α : Type) → (a' : α) → (motive : (a : α) → (h : Eq α a' a) → Type) →
    (refl : motive a' (Eq_refl α a')) → (a'' : α) → (t : Eq α a' a'') → motive a'' t) →
  (PUnit : Type) →
  (PUnit_unit : PUnit) →
  (PUnit_rec : (motive : (h : PUnit) → Type) → (unit : motive PUnit_unit) → (t : PUnit) → motive t) →
  (x : PUnit) → (y : PUnit) → Eq PUnit x y := by
  canonical_min

def Exists_imp :
  (Exists : (α : Type) → (p : (a : α) → Type) → Type) →
  (Exists_intro : (α : Type) → (p : (a : α) → Type) → (w : α) → (h : p w) → Exists α p) →
  (Exists_rec : (α : Type) → (p : (a : α) → Type) → (motive : (h : Exists α p) → Type) →
    (intro : (w : α) → (h : p w) → motive (Exists_intro α p w h)) → (t : Exists α p) → motive t) →
  (α : Type) →
  (p : (a : α) → Type) → (q : (a : α) → Type) →
  (f : (a : α) → (h : p a) → q a) → (h : Exists α p) → Exists α q := by
  canonical_min
