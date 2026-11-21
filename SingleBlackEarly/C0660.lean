import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0660 : checkSingleBlackFast (12, -10) 9178 .south (-8, -1) (-21, -10) = true := by
  decide +kernel

end LangtonsAnt
