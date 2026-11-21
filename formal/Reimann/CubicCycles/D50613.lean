import Reimann.Cubic

namespace Reimann.Cubic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 25000000 in
/-- The listed cycles account for every reduced pair at discriminant 50613. -/
theorem cycles_50613 : certificateAt 50613 = true := by decide +kernel

end Reimann.Cubic
