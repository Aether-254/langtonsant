import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0574 : checkSingleBlackFast (19, -1) 4792 .south (-13, -2) (-19, 2) = true := by
  decide +kernel

end LangtonsAnt
