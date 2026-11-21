import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0240 : checkSingleBlackFast (2, 8) 4543 .east (-2, -7) (-18, -4) = true := by
  decide +kernel

end LangtonsAnt
