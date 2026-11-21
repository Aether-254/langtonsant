import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0415 : checkSingleBlackFast (16, -3) 29784 .south (-11, -1) (-33, -17) = true := by
  decide +kernel

end LangtonsAnt
