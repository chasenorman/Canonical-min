import CanonicalMin

def Relation_TransGen_trans :
  (TransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (TransGen_single : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : r a b) → TransGen α r a b) →
  (TransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : TransGen α r a b) → (hbc : r b c) → TransGen α r a c) →
  (TransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : TransGen α r a a') → Type) →
    (single : (b : α) → (a' : r a b) → motive b (TransGen_single α r a b a')) → (tail : (b : α) → (c : α) → (a' : TransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (TransGen_tail α r a b c a' a'')) →
    (a'' : α) → (t : TransGen α r a a'') → motive a'' t) →
  (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : TransGen α r a b) → (hbc : TransGen α r b c) → TransGen α r a c := by
  canonical_min

def ReflGen_to_reflTransGen :
  (ReflGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflGen α r a a) →
  (ReflGen_single : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : r a b) → ReflGen α r a b) →
  (ReflGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflGen α r a a') → Type) → (refl : motive a (ReflGen_refl α r a)) →
    (single : (b : α) → (a' : r a b) → motive b (ReflGen_single α r a b a')) → (a'' : α) → (t : ReflGen α r a a'') → motive a'' t) →
  (ReflTransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflTransGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflTransGen α r a a) →
  (ReflTransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (rab : ReflTransGen α r a b) → (rbc : r b c) → ReflTransGen α r a c) →
  (ReflTransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflTransGen α r a a') → Type) →
    (refl : motive a (ReflTransGen_refl α r a)) → (tail : (b : α) → (c : α) → (a' : ReflTransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (ReflTransGen_tail α r a b c a' a'')) →
    (a''' : α) → (t : ReflTransGen α r a a''') → motive a''' t) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : ReflGen α r a b) → ReflTransGen α r a b := by
  canonical_min

def ReflGen_mono :
  (ReflGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflGen α r a a) →
  (ReflGen_single : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : r a b) → ReflGen α r a b) →
  (ReflGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflGen α r a a') → Type) → (refl : motive a (ReflGen_refl α r a)) →
    (single : (b : α) → (a' : r a b) → motive b (ReflGen_single α r a b a')) → (a'' : α) → (t : ReflGen α r a a'') → motive a'' t) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) →
  (p : (a : α) → (b : α) → Type) →
  (hp : (a : α) → (b : α) → (hr : r a b) → p a b) → (a : α) → (b : α) → (h : ReflGen α r a b) → ReflGen α p a b := by
  canonical_min

def ReflTransGen_trans :
  (ReflTransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflTransGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflTransGen α r a a) →
  (ReflTransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (rab : ReflTransGen α r a b) → (rbc : r b c) → ReflTransGen α r a c) →
  (ReflTransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflTransGen α r a a') → Type) →
    (refl : motive a (ReflTransGen_refl α r a)) → (tail : (b : α) → (c : α) → (a' : ReflTransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (ReflTransGen_tail α r a b c a' a'')) →
    (a''' : α) → (t : ReflTransGen α r a a''') → motive a''' t) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) →
  (a : α) → (b : α) → (c : α) →
  (hab : ReflTransGen α r a b) →
  (hbc : ReflTransGen α r b c) → ReflTransGen α r a c := by
  canonical_min

def ReflTransGen_head :
  (ReflTransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflTransGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflTransGen α r a a) →
  (ReflTransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (rab : ReflTransGen α r a b) → (rbc : r b c) → ReflTransGen α r a c) →
  (ReflTransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflTransGen α r a a') → Type) →
    (refl : motive a (ReflTransGen_refl α r a)) → (tail : (b : α) → (c : α) → (a' : ReflTransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (ReflTransGen_tail α r a b c a' a'')) →
    (a''' : α) → (t : ReflTransGen α r a a''') → motive a''' t) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) →
  (a : α) → (b : α) → (c : α) →
  (hab : r a b) →
  (hbc : ReflTransGen α r b c) → ReflTransGen α r a c := by
  canonical_min

def ReflTransGen_symmetric :
  (ReflTransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflTransGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflTransGen α r a a) →
  (ReflTransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (rab : ReflTransGen α r a b) → (rbc : r b c) → ReflTransGen α r a c) →
  (ReflTransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflTransGen α r a a') → Type) →
    (refl : motive a (ReflTransGen_refl α r a)) → (tail : (b : α) → (c : α) → (a' : ReflTransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (ReflTransGen_tail α r a b c a' a'')) →
    (a''' : α) → (t : ReflTransGen α r a a''') → motive a''' t) →
  (ReflTransGen_head : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : r a b) → (hbc : ReflTransGen α r b c) → ReflTransGen α r a c) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) →
  (h : (a : α) → (b : α) → (hr : r a b) → r b a) → (a : α) → (b : α) → (hab : ReflTransGen α r a b) → ReflTransGen α r b a := by
  canonical_min

def TransGen_to_reflTransGen :
  (TransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (TransGen_single : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : r a b) → TransGen α r a b) →
  (TransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : TransGen α r a b) → (hbc : r b c) → TransGen α r a c) →
  (TransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : TransGen α r a a') → Type) →
    (single : (b : α) → (a' : r a b) → motive b (TransGen_single α r a b a')) → (tail : (b : α) → (c : α) → (a' : TransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (TransGen_tail α r a b c a' a'')) →
    (a'' : α) → (t : TransGen α r a a'') → motive a'' t) →
  (ReflTransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflTransGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflTransGen α r a a) →
  (ReflTransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (rab : ReflTransGen α r a b) → (rbc : r b c) → ReflTransGen α r a c) →
  (ReflTransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflTransGen α r a a') → Type) →
    (refl : motive a (ReflTransGen_refl α r a)) → (tail : (b : α) → (c : α) → (a' : ReflTransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (ReflTransGen_tail α r a b c a' a'')) →
    (a''' : α) → (t : ReflTransGen α r a a''') → motive a''' t) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (hab : TransGen α r a b) → ReflTransGen α r a b := by
  canonical_min

def TransGen_trans_left :
  (TransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (TransGen_single : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : r a b) → TransGen α r a b) →
  (TransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : TransGen α r a b) → (hbc : r b c) → TransGen α r a c) →
  (TransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : TransGen α r a a') → Type) →
    (single : (b : α) → (a' : r a b) → motive b (TransGen_single α r a b a')) → (tail : (b : α) → (c : α) → (a' : TransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (TransGen_tail α r a b c a' a'')) →
    (a'' : α) → (t : TransGen α r a a'') → motive a'' t) →
  (ReflTransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflTransGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflTransGen α r a a) →
  (ReflTransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (rab : ReflTransGen α r a b) → (rbc : r b c) → ReflTransGen α r a c) →
  (ReflTransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflTransGen α r a a') → Type) →
    (refl : motive a (ReflTransGen_refl α r a)) → (tail : (b : α) → (c : α) → (a' : ReflTransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (ReflTransGen_tail α r a b c a' a'')) →
    (a''' : α) → (t : ReflTransGen α r a a''') → motive a''' t) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) →
  (a : α) → (b : α) → (c : α) →
  (hab : TransGen α r a b) →
  (hbc : ReflTransGen α r b c) → TransGen α r a c := by
  canonical_min

def TransGen_to_self :
  (TransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (TransGen_single : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : r a b) → TransGen α r a b) →
  (TransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : TransGen α r a b) → (hbc : r b c) → TransGen α r a c) →
  (TransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : TransGen α r a a') → Type) →
    (single : (b : α) → (a' : r a b) → motive b (TransGen_single α r a b a')) → (tail : (b : α) → (c : α) → (a' : TransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (TransGen_tail α r a b c a' a'')) →
    (a'' : α) → (t : TransGen α r a a'') → motive a'' t) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) →
  (trans : (a : α) → (b : α) → (c : α) → (hab : r a b) → (hbc : r b c) → r a c) →
  (a : α) → (b : α) →
  (h : TransGen α r a b) → r a b := by
  canonical_min

def TransGen_lift :
  (TransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (TransGen_single : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : r a b) → TransGen α r a b) →
  (TransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : TransGen α r a b) → (hbc : r b c) → TransGen α r a c) →
  (TransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : TransGen α r a a') → Type) →
    (single : (b : α) → (a' : r a b) → motive b (TransGen_single α r a b a')) → (tail : (b : α) → (c : α) → (a' : TransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (TransGen_tail α r a b c a' a'')) →
    (a'' : α) → (t : TransGen α r a a'') → motive a'' t) →
  (α : Type) → (β : Type) →
  (r : (a : α) → (b : α) → Type) →
  (p : (a : β) → (b : β) → Type) →
  (a : α) → (b : α) →
  (f : (a : α) → β) →
  (h : (a : α) → (b : α) → (hr : r a b) → p (f a) (f b)) →
  (hab : TransGen α r a b) → TransGen β p (f a) (f b) := by
  canonical_min

def TransGen_swap :
  (TransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (TransGen_single : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (h : r a b) → TransGen α r a b) →
  (TransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : TransGen α r a b) → (hbc : r b c) → TransGen α r a c) →
  (TransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : TransGen α r a a') → Type) →
    (single : (b : α) → (a' : r a b) → motive b (TransGen_single α r a b a')) → (tail : (b : α) → (c : α) → (a' : TransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (TransGen_tail α r a b c a' a'')) →
    (a'' : α) → (t : TransGen α r a a'') → motive a'' t) →
  (TransGen_head : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : r a b) → (hbc : TransGen α r b c) → TransGen α r a c) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) →
  (a : α) → (b : α) →
  (h : TransGen α r b a) →
  TransGen α (fun x y ↦ r y x) a b := by
  canonical_min

def ReflTransGen_swap :
  (ReflTransGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (ReflTransGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → ReflTransGen α r a a) →
  (ReflTransGen_tail : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (rab : ReflTransGen α r a b) → (rbc : r b c) → ReflTransGen α r a c) →
  (ReflTransGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (motive : (a' : α) → (h : ReflTransGen α r a a') → Type) →
    (refl : motive a (ReflTransGen_refl α r a)) → (tail : (b : α) → (c : α) → (a' : ReflTransGen α r a b) → (a'' : r b c) → (h : motive b a') → motive c (ReflTransGen_tail α r a b c a' a'')) →
    (a''' : α) → (t : ReflTransGen α r a a''') → motive a''' t) →
  (ReflTransGen_head : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → (c : α) → (hab : r a b) → (hbc : ReflTransGen α r b c) → ReflTransGen α r a c) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) →
  (a : α) → (b : α) →
  (h : ReflTransGen α r b a) →
  ReflTransGen α (fun x y ↦ r y x) a b := by
  canonical_min

def EqvGen_mono :
  (EqvGen : (α : Type) → (r : (a : α) → (b : α) → Type) → (a : α) → (b : α) → Type) →
  (EqvGen_rel : (α : Type) → (r : (a : α) → (b : α) → Type) → (x : α) → (y : α) → (h : r x y) → EqvGen α r x y) →
  (EqvGen_refl : (α : Type) → (r : (a : α) → (b : α) → Type) → (x : α) → EqvGen α r x x) →
  (EqvGen_symm : (α : Type) → (r : (a : α) → (b : α) → Type) → (x : α) → (y : α) → (h : EqvGen α r x y) → EqvGen α r y x) →
  (EqvGen_trans : (α : Type) → (r : (a : α) → (b : α) → Type) → (x : α) → (y : α) → (z : α) → (hxy : EqvGen α r x y) → (hyz : EqvGen α r y z) → EqvGen α r x z) →
  (EqvGen_rec : (α : Type) → (r : (a : α) → (b : α) → Type) → (motive : (a : α) → (a' : α) → (h : EqvGen α r a a') → Type) →
    (rel : (x : α) → (y : α) → (a : r x y) → motive x y (EqvGen_rel α r x y a)) →
    (refl : (x : α) → motive x x (EqvGen_refl α r x)) →
    (symm : (x : α) → (y : α) → (a : EqvGen α r x y) → (h : motive x y a) → motive y x (EqvGen_symm α r x y a)) →
    (trans :
      (x : α) → (y : α) → (z : α) → (a : EqvGen α r x y) → (a' : EqvGen α r y z) →
        (hxy : motive x y a) → (hyz : motive y z a') → motive x z (EqvGen_trans α r x y z a a')) →
    (a' : α) → (a'' : α) → (t : EqvGen α r a' a'') → motive a' a'' t) →
  (α : Type) →
  (r : (a : α) → (b : α) → Type) → (p : (a : α) → (b : α) → Type) →
  (hrp : (a : α) → (b : α) → (hr : r a b) → p a b) →
  (a : α) → (b : α) →
  (h : EqvGen α r a b) → EqvGen α p a b :=
  by canonical_min 20
