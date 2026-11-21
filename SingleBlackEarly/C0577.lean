import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0577 : checkSingleBlackFast (18, -1) 6524 .south (-12, 0) (-22, -4) = true := by
  decide +kernel

end LangtonsAnt
