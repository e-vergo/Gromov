-- TAIL-compliant structure
import Gromov.MainTheorem
import Gromov.ProofOfMainTheorem

-- Definitions (human review required)
import Gromov.Definitions.PolynomialGrowth
import Gromov.Definitions.WordMetric
import Gromov.Definitions.GrowthDegree
import Gromov.Definitions.Harmonic
import Gromov.Definitions.Poincare
import Gromov.Definitions.Descent
import Gromov.Definitions.VirtuallyNilpotent

-- Proofs (machine verified)
import Gromov.Proofs.Growth.GromovMain
import Gromov.Proofs.Cayley.Graph
import Gromov.Proofs.Growth.Polynomial
import Gromov.Proofs.VirtuallyNilpotent.Core
import Gromov.Proofs.Polycyclic.Core
import Gromov.Proofs.Polycyclic.ResiduallyFinite
import Gromov.Proofs.VirtuallyNilpotent.NilpotencyClass
import Gromov.Proofs.Growth.Nilpotent
import Gromov.Proofs.Growth.Abelian
import Gromov.Proofs.Descent.Main
import Gromov.Proofs.Harmonic.Core
import Gromov.Proofs.Poincare.Main

-- Polycyclic infrastructure
import Gromov.Proofs.Polycyclic.Abelian
import Gromov.Proofs.Polycyclic.Extensions
import Gromov.Proofs.Polycyclic.Fitting
import Gromov.Proofs.Polycyclic.Malcev

-- Schreier infrastructure
import Gromov.Proofs.Schreier.CosetReps
import Gromov.Proofs.Schreier.WordBounds

-- Growth infrastructure
import Gromov.Proofs.Growth.Fibration
import Gromov.Proofs.Growth.KernelDegree

-- Harmonic infrastructure
import Gromov.Proofs.Harmonic.Spectral
import Gromov.Proofs.Harmonic.Existence
import Gromov.Proofs.Harmonic.FiniteDim

-- Representation infrastructure
import Gromov.Proofs.Representation.CompactLie
import Gromov.Proofs.Representation.QuotientExtraction
