import CanonicalMin

def Eq_symm :
  (Eq : (α : Type) → (x : α) → (y : α) → Type) →
  (Eq_refl : (α : Type) → (x : α) → Eq α x x) →
  (Eq_rec : (α : Type) → (a' : α) → (motive : (a : α) → (h : Eq α a' a) → Type) →
    (refl : motive a' (Eq_refl α a')) → (a'' : α) → (t : Eq α a' a'') → motive a'' t) →
  (α : Type) → (a : α) → (b : α) → (h : Eq α a b) → Eq α b a := by
  canonical_min

def Eq_trans :
  (Eq : (α : Type) → (x : α) → (y : α) → Type) →
  (Eq_refl : (α : Type) → (x : α) → Eq α x x) →
  (Eq_rec : (α : Type) → (a' : α) → (motive : (a : α) → (h : Eq α a' a) → Type) →
    (refl : motive a' (Eq_refl α a')) → (a'' : α) → (t : Eq α a' a'') → motive a'' t) →
  (α : Type) → (a : α) → (b : α) → (c : α) → (hab : Eq α a b) → (hbc : Eq α b c) → Eq α a c := by
  canonical_min

def Eq_congrArg :
  (Eq : (α : Type) → (x : α) → (y : α) → Type) →
  (Eq_refl : (α : Type) → (x : α) → Eq α x x) →
  (Eq_rec : (α : Type) → (a' : α) → (motive : (a : α) → (h : Eq α a' a) → Type) →
    (refl : motive a' (Eq_refl α a')) → (a'' : α) → (t : Eq α a' a'') → motive a'' t) →
  (α : Type) → (β : Type) → (f : (a : α) → β) → (a₁ : α) → (a₂ : α) → (h : Eq α a₁ a₂) → Eq β (f a₁) (f a₂) := by
  canonical_min

def Eq_congr :
  (Eq : (α : Type) → (x : α) → (y : α) → Type) →
  (Eq_refl : (α : Type) → (x : α) → Eq α x x) →
  (Eq_rec : (α : Type) → (a' : α) → (motive : (a : α) → (h : Eq α a' a) → Type) →
    (refl : motive a' (Eq_refl α a')) → (a'' : α) → (t : Eq α a' a'') → motive a'' t) →
  (Pi : (α : Type) → (β : (a : α) → Type) → Type) →
  (Pi_f : (α : Type) → (β : (a : α) → Type) → (self : Pi α β) → (a : α) → β a) →
  (α : Type) → (β : Type) → (f₁ : Pi α (fun _ ↦ β)) → (f₂ : Pi α (fun _ ↦ β)) → (a₁ : α) → (a₂ : α) →
  (h₁ : Eq (Pi α (fun _ ↦ β)) f₁ f₂) → (h₂ : Eq α a₁ a₂) → Eq β (Pi_f α (fun _ ↦ β) f₁ a₁) (Pi_f α (fun _ ↦ β) f₂ a₂) := by
  canonical_min

def Eq_congrFun :
  (Eq : (α : Type) → (x : α) → (y : α) → Type) →
  (Eq_refl : (α : Type) → (x : α) → Eq α x x) →
  (Eq_rec : (α : Type) → (a' : α) → (motive : (a : α) → (h : Eq α a' a) → Type) →
    (refl : motive a' (Eq_refl α a')) → (a'' : α) → (t : Eq α a' a'') → motive a'' t) →
  (Pi : (α : Type) → (β : (a : α) → Type) → Type) →
  (Pi_f : (α : Type) → (β : (a : α) → Type) → (self : Pi α β) → (a : α) → β a) →
  (α : Type) → (β : (a : α) → Type) → (f : Pi α β) → (g : Pi α β) →
  (h : Eq (Pi α β) f g) → (a : α) → Eq (β a) (Pi_f α β f a) (Pi_f α β g a) := by
  canonical_min

def Eq_mp :
  (Eq : (x : Type) → (y : Type) → Type) →
  (Eq_refl : (x : Type) → Eq x x) →
  (Eq_rec : (a' : Type) → (motive : (a : Type) → (h : Eq a' a) → Type) →
    (refl : motive a' (Eq_refl a')) → (a'' : Type) → (t : Eq a' a'') → motive a'' t) →
  (P : Type) → (Q : Type) → (h : Eq P Q) → (p : P) → Q := by
  canonical_min
