import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0483 : checkSingleBlackFast (7, 14) 7926 .south (-13, -4) (-18, -19) = true := by
  decide +kernel

end LangtonsAnt
