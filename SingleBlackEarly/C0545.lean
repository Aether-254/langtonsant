import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0545 : checkSingleBlackFast (8, -4) 14922 .south (-12, 1) (-27, -12) = true := by
  decide +kernel

end LangtonsAnt
