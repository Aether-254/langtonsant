import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2078 : checkSingleBlackFast2 (-78, -58) 16964 .north (34, 24) (-60, -40) = true := by
  decide +kernel

end LangtonsAnt
