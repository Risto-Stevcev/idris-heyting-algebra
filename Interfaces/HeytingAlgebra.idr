module Interfaces.HeytingAlgebra

import Control.Algebra.Lattice
import Interfaces.Verified

%hide Prelude.Monad.join


--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

interface (BoundedJoinSemilattice a, BoundedMeetSemilattice a, Ord a) => HeytingAlgebra a where
  not : a -> a
  implies : a -> a -> a


--------------------------------------------------------------------------------
-- Verified Interfaces
--------------------------------------------------------------------------------

interface (VerifiedJoinSemilattice a, BoundedJoinSemilattice a) => VerifiedBoundedJoinSemilattice a where
  boundedJoinSemilatticeIdentity : (x : a) -> join x Control.Algebra.Lattice.bottom = x

interface (VerifiedMeetSemilattice a, BoundedMeetSemilattice a) => VerifiedBoundedMeetSemilattice a where
  boundedMeetSemilatticeIdentity : (x : a) -> meet x Control.Algebra.Lattice.top = x

interface (VerifiedJoinSemilattice a, VerifiedMeetSemilattice a, HeytingAlgebra a) => VerifiedHeytingAlgebra a where
  total heytingAlgebraPseudoComplement : (x : a) -> HeytingAlgebra.not x = x `implies` Control.Algebra.Lattice.bottom
  total heytingAlgebraRelativePseudoComplement : (x, y, z : a) -> (z `meet` x) <= y = z <= (x `implies` y)


--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

JoinSemilattice Bool where
  join x y = x || y

BoundedJoinSemilattice Bool where
  bottom = False

MeetSemilattice Bool where
  meet x y = x && y

BoundedMeetSemilattice Bool where
  top = True

HeytingAlgebra Bool where
  not = Prelude.Bool.not
  implies x y = (not x) || y


--------------------------------------------------------------------------------
-- Verified Implementations
--------------------------------------------------------------------------------

VerifiedJoinSemilattice Bool where
  joinSemilatticeJoinIsAssociative False False False = Refl
  joinSemilatticeJoinIsAssociative False False True = Refl
  joinSemilatticeJoinIsAssociative False True False = Refl
  joinSemilatticeJoinIsAssociative False True True = Refl
  joinSemilatticeJoinIsAssociative True False False = Refl
  joinSemilatticeJoinIsAssociative True False True = Refl
  joinSemilatticeJoinIsAssociative True True False = Refl
  joinSemilatticeJoinIsAssociative True True True = Refl
  joinSemilatticeJoinIsCommutative False False = Refl
  joinSemilatticeJoinIsCommutative False True = Refl
  joinSemilatticeJoinIsCommutative True False = Refl
  joinSemilatticeJoinIsCommutative True True = Refl
  joinSemilatticeJoinIsIdempotent False = Refl
  joinSemilatticeJoinIsIdempotent True = Refl

VerifiedBoundedJoinSemilattice Bool where
  boundedJoinSemilatticeIdentity False = Refl
  boundedJoinSemilatticeIdentity True = Refl

VerifiedMeetSemilattice Bool where
  meetSemilatticeMeetIsAssociative False False False = Refl
  meetSemilatticeMeetIsAssociative False False True = Refl
  meetSemilatticeMeetIsAssociative False True False = Refl
  meetSemilatticeMeetIsAssociative False True True = Refl
  meetSemilatticeMeetIsAssociative True False False = Refl
  meetSemilatticeMeetIsAssociative True False True = Refl
  meetSemilatticeMeetIsAssociative True True False = Refl
  meetSemilatticeMeetIsAssociative True True True = Refl
  meetSemilatticeMeetIsCommutative False False = Refl
  meetSemilatticeMeetIsCommutative False True = Refl
  meetSemilatticeMeetIsCommutative True False = Refl
  meetSemilatticeMeetIsCommutative True True = Refl
  meetSemilatticeMeetIsIdempotent False = Refl
  meetSemilatticeMeetIsIdempotent True = Refl

VerifiedBoundedMeetSemilattice Bool where
  boundedMeetSemilatticeIdentity False = Refl
  boundedMeetSemilatticeIdentity True = Refl

VerifiedHeytingAlgebra Bool where
  heytingAlgebraPseudoComplement False = Refl
  heytingAlgebraPseudoComplement True = Refl
  heytingAlgebraRelativePseudoComplement False False False = Refl
  heytingAlgebraRelativePseudoComplement False False True = Refl
  heytingAlgebraRelativePseudoComplement False True False = Refl
  heytingAlgebraRelativePseudoComplement False True True = Refl
  heytingAlgebraRelativePseudoComplement True False False = Refl
  heytingAlgebraRelativePseudoComplement True False True = Refl
  heytingAlgebraRelativePseudoComplement True True False = Refl
  heytingAlgebraRelativePseudoComplement True True True = Refl
