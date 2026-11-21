import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0576 : checkSingleBlackFast (20, -2) 29602 .south (-21, 11) (-24, -18) = true := by
  decide +kernel

end LangtonsAnt
