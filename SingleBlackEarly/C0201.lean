import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0201 : checkSingleBlackFast (10, 4) 8484 .south (-11, 5) (-15, -17) = true := by
  decide +kernel

end LangtonsAnt
