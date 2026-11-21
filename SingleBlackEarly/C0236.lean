import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0236 : checkSingleBlackFast (4, 9) 5216 .south (-2, -5) (-18, -13) = true := by
  decide +kernel

end LangtonsAnt
