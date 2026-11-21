import Reimann.Cubic

namespace Reimann.Cubic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 25000000 in
/-- The listed cycles account for every reduced pair at discriminant 456. -/
theorem cycles_456 : certificateAt 456 = true := by decide +kernel

end Reimann.Cubic
