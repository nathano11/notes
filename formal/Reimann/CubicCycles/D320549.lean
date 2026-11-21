import Reimann.Cubic

namespace Reimann.Cubic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 25000000 in
/-- The listed cycles account for every reduced pair at discriminant 320549. -/
theorem cycles_320549 : certificateAt 320549 = true := by decide +kernel

end Reimann.Cubic
