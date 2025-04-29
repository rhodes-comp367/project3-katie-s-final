open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List using (_∷_; [])renaming (List to List')

data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
    snoc : List A → A → List A

-- length of the list as a nat
length : {A : Set} → List A → Nat
length nil = zero
length (cons _ xs) = suc (length xs)
length (snoc xs _) = suc (length xs)

-- sum of all the elements of a nat list
sum : List Nat → Nat
sum nil = zero
sum (cons x xs) = x + sum xs
sum (snoc xs x) = sum xs + x

-- helper for all function with boolean properties
and : Bool → Bool → Bool
and false _ = false
and true x = x

-- returning if all the elements in a bool list are the same
all : List Bool → Bool
all nil = true
all (cons x xs) = and x (all xs)
all (snoc xs x) = and x (all xs)

-- adding two lists together
concat : {A : Set} → List A → List A → List A
concat nil ys = ys
concat (cons x xs) ys = concat xs (snoc ys x)
concat (snoc xs x) ys = concat xs (cons x ys)

-- helper for length-eq, using cons adds one to the length
length-suc : {A : Set} → (xs : List A) → (x : A) → length (cons x xs) ≡ suc (length xs)
length-suc xs x = refl

-- proving the length is the same whether you use snoc or cons
length-eq : {A : Set} → (xs : List A) → (x : A) → length (snoc xs x) ≡ length (cons x xs)
length-eq xs x rewrite length-suc xs x = refl

-- cons is the opposite of snoc
reverse : {A : Set} → List A → List A
reverse nil = nil
reverse (cons x xs) = snoc (reverse xs) x
reverse (snoc xs x) = cons x (reverse xs)

--map a function onto the list
map : {A B : Set} → (A → B) → List A → List B
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)
map f (snoc xs x) = snoc (map f xs) (f x)

-- take the first n elements of a list
-- idea for this function came from chatGPT - which only created skeleton, no answers
take : {A : Set} → Nat → List A → List A
take zero _ = nil
take (suc n) nil = nil
take (suc n) (cons x xs) = cons x (take n xs)
take (suc n) (snoc xs x) = cons x (take n xs)

-- take the last n elements from a list
take' : {A : Set} → Nat → List A → List A
take' zero _ = nil
take' (suc n) nil = nil
take' (suc n) (cons x xs) = snoc (take n xs) x
take' (suc n) (snoc xs x) = snoc (take n xs) x

--maybe
data Maybe (A : Set) : Set where
    nothing : Maybe A 
    just : A → Maybe A

-- pointer to the head of the list
head : {A : Set} → List A → Maybe A 
head nil = nothing
head (cons x xs) = just x
head (snoc xs x) = head xs

-- pointer to the tail of the list
tail : {A : Set} → List A → Maybe A 
tail nil = nothing
tail (cons x xs) = just x
tail (snoc xs x) = tail xs

-- proving two lists are equal
data ListEq {A : Set} : List A → List A → Set where
    eq-refl : ∀ {xs} → ListEq xs xs
    eq-xnil : ∀ {x : A} → (cons x nil) ≡ (snoc nil x) → ListEq nil nil
    eq-cons : ∀ {x y : A} → {xs ys : List A} → (cons x (snoc xs y)) ≡ (cons x (snoc xs y)) → ListEq ys ys
    eq-snoc : ∀ {x y : A} → {xs ys : List A} → (snoc (cons x xs) y) ≡ (snoc (cons x xs) y) → ListEq ys ys
    eq-xsys : ∀ {x y : A} → {xs ys : List A} → (cons x (snoc xs y)) ≡ (snoc (cons x xs) y) → ListEq xs ys

to-list-help : {A : Set} → List A → List' A → List' A
to-list-help nil x = x
to-list-help (cons x xs) n = x ∷ to-list-help xs n 
to-list-help (snoc xs x) n = to-list-help xs (x ∷ n)

--used chatGPT to help set up this function
to-list' : {A : Set} → List A → List' A
to-list' nil = List'.[]
to-list' (cons x xs) = x ∷ to-list' xs
to-list' (snoc xs x) = to-list-help xs (x ∷ List'.[])

to-list-eq : {A : Set} → {xs ys : List A} → ListEq xs ys → to-list' xs ≡ to-list' ys
to-list-eq {xs = xs} {ys} eq-refl = refl
to-list-eq {xs = nil} {ys = nil} (eq-xnil eq) = refl
to-list-eq (eq-cons eq) = refl
to-list-eq (eq-snoc eq) = refl
to-list-eq (eq-xsys eq) rewrite eq = {!   !} 
--cannot figure out a rewrite that sets this up, this should work to apply the eq case



