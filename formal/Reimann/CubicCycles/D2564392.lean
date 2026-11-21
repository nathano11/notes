import Reimann.Cubic

namespace Reimann.Cubic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 25000000 in
/-- The listed cycles account for every reduced pair at discriminant 2564392. -/
theorem cycles_2564392 : certificateAt 2564392 = true := by decide +kernel

end Reimann.Cubic
