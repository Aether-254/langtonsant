import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0360 : checkSingleBlackFast (13, 0) 5034 .south (-3, -13) (-10, -12) = true := by
  decide +kernel

end LangtonsAnt
