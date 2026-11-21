import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0649 : checkSingleBlackFast (9, -11) 10290 .south (-16, -2) (-29, -11) = true := by
  decide +kernel

end LangtonsAnt
