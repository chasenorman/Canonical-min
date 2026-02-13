import CanonicalMin

def Nat_zero_le :
  (Nat : Type) →
  (Nat_zero : Nat) →
  (Nat_succ : (n : Nat) → Nat) →
  (Nat_rec : (motive : (n : Nat) → Type) → (zero : motive Nat_zero) →
    (succ : (n : Nat) → (h : motive n) → motive (Nat_succ n)) → (t : Nat) → motive t) →
  (le : (n : Nat) → (m : Nat) → Type) →
  (le_refl : (n : Nat) → le n n) →
  (le_step : (n : Nat) → (m : Nat) → (h : le n m) → le n (Nat_succ m)) →
  (le_rec : (n : Nat) → (motive : (a : Nat) → (h : le n a) → Type) → (refl : motive n (le_refl n)) →
    (step : (m : Nat) → (a : le n m) → (h : motive m a) → motive (Nat_succ m) (le_step n m a)) → (a' : Nat) → (t : le n a') → motive a' t) →
  (n : Nat) → le Nat_zero n := by
  canonical_min

def Nat_succ_le_succ :
  (Nat : Type) →
  (Nat_zero : Nat) →
  (Nat_succ : (n : Nat) → Nat) →
  (Nat_rec : (motive : (n : Nat) → Type) → (zero : motive Nat_zero) →
    (succ : (n : Nat) → (h : motive n) → motive (Nat_succ n)) → (t : Nat) → motive t) →
  (le : (n : Nat) → (m : Nat) → Type) →
  (le_refl : (n : Nat) → le n n) →
  (le_step : (n : Nat) → (m : Nat) → (h : le n m) → le n (Nat_succ m)) →
  (le_rec : (n : Nat) → (motive : (a : Nat) → (h : le n a) → Type) → (refl : motive n (le_refl n)) →
    (step : (m : Nat) → (a : le n m) → (h : motive m a) → motive (Nat_succ m) (le_step n m a)) → (a' : Nat) → (t : le n a') → motive a' t) →
  (n : Nat) → (m : Nat) → (h : le n m) → le (Nat_succ n) (Nat_succ m) := by
  canonical_min

def Nat_le_trans :
  (Nat : Type) →
  (Nat_zero : Nat) →
  (Nat_succ : (n : Nat) → Nat) →
  (Nat_rec : (motive : (n : Nat) → Type) → (zero : motive Nat_zero) →
    (succ : (n : Nat) → (h : motive n) → motive (Nat_succ n)) → (t : Nat) → motive t) →
  (le : (n : Nat) → (m : Nat) → Type) →
  (le_refl : (n : Nat) → le n n) →
  (le_step : (n : Nat) → (m : Nat) → (h : le n m) → le n (Nat_succ m)) →
  (le_rec : (n : Nat) → (motive : (a : Nat) → (h : le n a) → Type) → (refl : motive n (le_refl n)) →
    (step : (m : Nat) → (a : le n m) → (h : motive m a) → motive (Nat_succ m) (le_step n m a)) → (a' : Nat) → (t : le n a') → motive a' t) →
  (n : Nat) → (m : Nat) → (k : Nat) → (hnm : le n m) → (hmk : le m k) → le n k := by
  canonical_min

def sSup_inter_le :
  (And : (α : Type) → (β : Type) → Type) →
  (And_mk : (α : Type) → (β : Type) → (a : α) → (b : β) → And α β) →
  (And_left : (α : Type) → (β : Type) → (self : And α β) → α) →
  (And_right : (α : Type) → (β : Type) → (self : And α β) → β) →
  (α : Type) →
  (sSup : (set : (a : α) → Type) → α) →
  (le : (a : α) → (b : α) → Type) →
  (inf : (a : α) → (b : α) → α) →
  (le_sSup : (s : (a : α) → Type) → (a : α) → (h : s a) → le a (sSup s)) →
  (sSup_le : (s : (a : α) → Type) → (a : α) → (h : (b : α) → (sb : s b) → le b a) → le (sSup s) a) →
  (le_inf : (a : α) → (b : α) → (c : α) → (hab : le a b) → (hac : le a c) → le a (inf b c)) →
  (s : (a : α) → Type) → (t : (a : α) → Type) →
  le (sSup (fun x => And (s x) (t x))) (inf (sSup s) (sSup t)) := by
  canonical_min
