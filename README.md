Note that the code presented below has not been fed through GHC so it may contain errors.

# Why lenses

Ignoring the Equality layer, the lens that is the least restrictive in how it can be used (has the least
constrained type) is an Iso

```
type Iso s t a b = forall p f. (Profunctor p, Functor f) => p a (f b) -> p s (f t)
```

This is a mapping from any relationship between `a` and a transformation of `b` to a corresponding relationship
between `s` and the same transformation of `t`.  The transformation allows a large selection in choices of what
is related independent of the structure of the relationship.  For example

```
f b = a           -->  p a a
f b = (a,b)       -->  p a (a,b)
f b = Either a b  -->  p a (Either a b)
p b = c -> b      -->  p a (c -> b)
```

Together the choice of `p` and `f` provide a very general framework for moving from working with `a`s and `b`s to
working with `s`s and `t`s.  One interesting idea explored in the mezzolens library is to fold `f` into `p`.  This
gives very similar expressiveness as we can define the profunctor `(h f) a b = p a (f b)`.

All other lenses are Isos with additional restrictions on how they can be used (e.g., `f` has to be applicative
too, `p` has to be `(->)`, etc.).  While additional restrictions on the Iso type gives the lens creator more and/or
required functionality to create the lens with (e.g., adding the restriction applicative allows you to use `pure`
and `(<*>)` in addition to `(<$>)` in creating the lens), they also make the resulting lens less useful as any
restrictions must be satisfied by the person using the lens (e.g., their `f` now has to be applicative too).

```
less restrictions on lens type              ->  more restrictions on lens type
 
less lenses as harder/impossible to create  ->  more lenses as easier/possible to create
more uses as of lenses as less restricted   ->  less uses of lenses as more restricted
```
 
This is what gives rise to the lens hierarchy.  As you go down in it, the number of lenses you can use increases
(e.g., many Setters compared to Isos), but the ways in which those lenses can be used decreases (e.g., Setters can
only be used for setting, while Isos can be used for folding, setting, getting, traversing, etc.).  The beauty of
the framework though is composability.  Any lens in the hierarchy can be composed with any other lens in the
hierarchy with `(.)` and a new lens exists at the level of the most restricted lens that went into it.

# Monad lenses via monad transformers

Inevitably we find ourselves having to work with the real world though and wonder if there is something similarly
powerful for abstracting relationships across monad values.  Could we define an equivalently general encoding for
the characteristic functions defined over monads instead of just the standard values?

```
        Value Iso                 Monad Iso
to:     s -> a            mto:    s -> m a
from:   b -> t            mfrom:  b -> m t

       Value Lens                 Monad Lens
get:   s -> a             mget:   s -> m a
set:   s -> b -> t        mset:   s -> b -> m t

       Value Prism                Monad Prism
to'    s -> Either a t    mto':   s -> m (Either a t)
from:  b -> t             mfrom:  b -> m t

etc.
```

An initial guess of such an encoding might be something like

```
(Profunctor p, Functor f, Monad m) => p a (f (m b)) -> p s (f (m t))
```

While playing with this it became evident that what we really want is not a transformation of the value `m b`, but
rather a transformation of the monad `h m`, where we use `h` to represent the transformation instead of the more
standard `t` to avoid confusion with the standard use of `t` as the ultimate result type in lenses.  We also seems
need to make the contravariant part of the profunctor (input) monadic to feed it our values.

```
(Profunctor p, Monadtrans h, Monad m, Monad (h m)) => p (m a) (h m b)) -> p (m s) (h m t))
```

Using this, we get the same sort of large selection in choices of what is related independent of the structure of the
relationship and the ability to encode the underlying transformations.  For example

```
h m b = m a           -->  p (m a) (m a)
h m b = m (a,b)       -->  p (m a) (m (a,b))
h m b = m Either a b  -->  p (m a) (m (Either a b))
h m b = c -> m b      -->  p (m a) (c -> m b)
```
```haskell
toIso :: (Profunctor p, Monadtrans h, Monad m, Monad (h m))
      => (s -> m a)               -- to
      -> (b -> m t)               -- from
      -> p (m a) (h m b))         -- input relationship
      -> p (m s) (h m t))         -- output relationship
toIso sa bt = dimap sa (>>= lift . bt)
```
```haskell
toLens :: (Monadtrans h, Monad m, Monad (h m))
       => (s -> m a)              -- get
       -> (s -> b -> m t)         -- set
       -> (m a -> h m b)          -- input relationship
       -> (m s -> h m t)          -- output relationship
toLens sa sbt afb s = afb (sa s) >>= lift . sbt s
```

When we get to Prisms though, we run into the problem that we managed to dodge above by having the contravariant
(input) part of our profunctor be a monad.  To use the additional profunctor functionality offered by constraints
like Choice, we need to be able to form the non-monadic inputs they required.  This requires some additional
functionality as all our inputs are locked inside of monads.  What we want is something like

```haskell
lmap' :: (a -> m b) -> p b (m c) -> p a (m c)  -- not a standard function
```

There are a variety of possibilities for this.  We could limit ourselves to Representable profunctors so we can
directly access the contravariant part (input) and feed it with `(>>=)`.  We could require Traversing or Mapping so
we can lift it to being over the monad via the `map'` function.  This last option seems to be the least restrictive
as `lmap'` and `map'` turn out to be equivalent and `lmap'` trivially exists for all Representable profunctors.

```haskell
map' :: p a b -> p (m a) (m b)
map' = lmap' id . fmap return
```
```haskell
lmap' :: Mapping p => (a -> m b) -> p b (m c) -> p a (m c)
lmap' amb = dimap amb join . map'
```
```haskell
lmap' :: Representable p => (a -> m b) -> p b (m c) -> p a (m c)
lmap' amb = tabulate . (>>= sieve pbmc) . amb
```
```haskell
toPrism :: (Mapping p, Monadtrans h, Monad m, Monad (h m))  -- 
        => (s -> m (Either a t))  -- to'
        -> (b -> m t)             -- from
        -> p a (h m b)            -- input relationship
        -> p s (h m t)            -- output relationship
toPrism seat bt = dimap (lift . seat) (>>= either (>>= lift . bt) return) . map' . left'
```

With the ability to feed in monadic inputs, we have also dropped wrapping the contravariant part of the profunctor
(input) in a monad.  This brings us back to the standard lens format where we are now simply using transformed
monads as the functor on the covariant part of the profunctor (output)

```
(Mapping p, Monadtrans h, Monad m, Monad (h m)) => p a ((h m) b)) -> p s ((h m) t)
```

These are just regular lenses with some new constraints.  This means they fit beautifully into the hierarchy
composing fine with all the existing lenses.

None of the existing lens functions instantiate their lenses with monad transformers though, so we now turn our
attention to how we would write functions that uses the lenses by writing the basic getter and setter

```haskell
viewM :: MonadReader s r => ((a -> WriterT a m b) -> (s -> WriterT a m t)) -> r (m a)
viewM l = reader (execWriterT . l (\a -> WriterT $ return (a,a)))
```
```haskell
overM :: ((a -> IdentityT a m b) -> (s -> IdentityT s m t)) -> (a -> m b) -> s -> m t
overM l amb = runIdentity . l (IdentityT . amb)
```

An interesting point here is that, unlike how the standard getter, the monad getter cannot be defined in terms of a
constant monad transformer because no such thing exists.  This is because the essence of a monad over applicative
is the ability to flatten layers.  You need the values to allow them to be merged (e.g., if I try and merge two
constant layers I immediately run into the problem that I don't have the inner layer to merge).  This implies you
cannot define Fold only monad transformer based lenses as they do not carry results.

# Monad lenses via applicative composition

It does seem for the use case of `viewM` though that what we are really doing it just going to the inner most
point, taking what is there, and then carrying it out.  What flattening is happening?  Why do we have to worry
about what happens after we get a hold of our value?  Would it be sufficient in a case like this for the
transformed monad to just be applicative?  Consider the `toPrism` example lens again

```haskell
toPrism :: (Mapping p, Monadtrans h, Monad m, Monad (h m))  -- 
        => (s -> m (Either a t))  -- to'
        -> (b -> m t)             -- from
        -> p a (h m b)            -- input relationship
        -> p s (h m t)            -- output relationship
toPrism seat bt pahb = dimap prefix suffix peatehbt
  where
    peatehbt :: p (h m (Either a t) (h m (Either (h m b) t))
    peatehbt = map' . left $ pahb
    
    prefix :: (s -> h m (Either a t))
    prefix = lift . seat
    
    suffix :: h m (Either (h m b) t) -> h m t
    suffix = (>>= either (>>= lift . bt) return)
```

There is a flattening of the transformed monad in the `suffix` function.  We squash the outer `h m` with the
potential inner `h m` in `Either` because we need to look inside the monad to determine whether `to'` (argument
`seat`) broke `s` down into an `a` or a `t`.  The actually takes place in `m` though and we can reflect that

```haskell
toPrism' :: (Mapping p, Monadtrans h, Monad m, Monad (h m))  -- 
        => (s -> m (Either a t))  -- to'
        -> (b -> m t)             -- from
        -> p a (h m b)            -- input relationship
        -> p s (h m t)            -- output relationship
toPrism' seat bt pahb = dimap prefix (magic . suffix) peatehbt
  where
    peatehbt :: p (m (Either a t) (m (Either (h m b) t))
    peatehbt = map' . left $ pahb
    
    prefix :: (s -> m (Either a t))
    prefix = seat
    
    suffix :: m (Either (h m b) t) -> m (h m (m t))
    suffix = fmap $ either (fmap from) (return . return)

    magic :: m (h m (m t)) -> h m t
    magic = ???
```

It seems the transformed monad `h m` doesn't actually have to be a monad as we don't need to squash layers of it.
Rather we need to squash layers of the original `m` across `h m`.  It follows that we should likely examine the
class of transformers given by composition with an applicative functor as composition of applicative functors gives
an applicative functor.  There are two ways we can compose an applicative functor `g` with `m` for our transformer

```
h m = Compose g m  -->  magicL :: m (Compose g m (m t)) -> Compose g m t  -->  m (g (m (m t))) -> g (m t)
h m = Compose m g  -->  magicR :: m (Compose m g (m t)) -> Compose m g t  -->  m (m (g (m t))) -> m (g t)
```

In the first case we need to be able to push the first `m` inside of `g` where we can then join the inner `m`s.
This requires `g` to be distributive, which, according to the documentation distributive documentation means `g m
a` isomorphic to `x -> m a` for some `x`.  The interesting thing about this composition is `(Compose g m) a = g (m
a)`, so what we really have is just a regular lens with monad wrapped covariant (output) parts

```
((Compose g m) b) -> p s ((Compose g m) t)  -->  p a (g (m b) -> p s (g (m t))
```
```haskell
magicL :: m (Compose g m (m t)) -> Compose g m t
magicL = Compose . fmap (join . join) . distribute . fmap getCompose
```

Appart from the Identity functor, which makes no difference on which side you compose it, our standard functors are
not distributive though, so we turn our attention to the second case.  In this case we need to pull the final `m`
out of the `g` where we can then join the outer `m`s.  This requires `g` to be Traversable

```haskell
magic = magicR :: m (Compose m g (m t)) -> Compose m g t
magic = magicR = Compose . join . join . fmap (fmap sequenceA . getCompose)
```

Having completed the `toPrism'` lens, we can now return to writing a revised getter that does not needlessly carry
values around with it.  The Const functor is both applicative and traversable, so

```haskell
viewM' :: (MonadReader s r, Monad m)  => ((a -> Compose m (Const a) b) -> (s -> Compose m (Const a) t)) -> r (m a)
viewM' l = reader (fmap getConst . getCompose . l (Compose . return . Const)))
```

This re-opens the door to Fold only monad transformer based lenses.

# Combined value and monad lens functions

It is also interesting to note that this function is almost identical to the official `view` function across
standard values.  We even use the same `Const` functor.  In fact, if we choose `m` to be the identity monad, it
collapses to the standard `view` function modulo wrapping and unwrapping with Identity.  Examining the setter
reveals the same thing is true

```
IdentityT m a = m a = m (Identity a) = Compose m Identity a
```
```haskell
overM' :: (Monad m) => ((a -> Compose m Identity b) -> (s -> Compose m Identity t) -> (a -> m b) -> s -> m t
overM' l amb = fmap getIdentity . getCompose . l (Compose . fmap Identity . amb)
```

Again we use the exact same functor as the official `over` function across standard values.  Again it collapses to
the standard `over` function modulo the Identity wrapping when we choose `m` to be the identity monad.  With the
power of coercions now in GHC, we can actually have the compiler make the transformation for us

```haskell
view :: (MonadReader s r)  => ((a -> Const a b) -> (s -> Const a t)) -> r a
view = coerce viewM'
```
```haskell
over :: ((a -> Identity b) -> (s -> Identity t) -> (a -> b) -> s -> t
over = coerce overM'
```
