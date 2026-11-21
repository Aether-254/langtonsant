import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1790 : checkSingleBlackFast (-52, -34) 28147 .east (29, 17) (-12, -39) = true := by
  decide +kernel

end LangtonsAnt
