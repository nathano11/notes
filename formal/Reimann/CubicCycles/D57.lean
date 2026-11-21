import Reimann.Cubic

namespace Reimann.Cubic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 25000000 in
/-- The listed cycles account for every reduced pair at discriminant 57. -/
theorem cycles_57 : certificateAt 57 = true := by decide +kernel

end Reimann.Cubic
