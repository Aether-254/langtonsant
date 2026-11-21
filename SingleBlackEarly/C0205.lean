import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0205 : checkSingleBlackFast (9, 5) 6604 .south (-17, -6) (-23, -6) = true := by
  decide +kernel

end LangtonsAnt
