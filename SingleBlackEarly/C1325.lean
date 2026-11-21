import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1325 : checkSingleBlackFast (-12, 17) 12910 .north (3, 0) (-30, -9) = true := by
  decide +kernel

end LangtonsAnt
