import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0251 : checkSingleBlackFast (11, 6) 14704 .south (-11, 1) (-25, -13) = true := by
  decide +kernel

end LangtonsAnt
