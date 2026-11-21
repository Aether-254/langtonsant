import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0036 : checkSingleBlackFast (-1, 3) 1084 .south (-3, -3) (-9, -5) = true := by
  decide +kernel

end LangtonsAnt
