import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0929 : checkSingleBlackFast (-13, 12) 11418 .south (-8, -2) (-27, -15) = true := by
  decide +kernel

end LangtonsAnt
