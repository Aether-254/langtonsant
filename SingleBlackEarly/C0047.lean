import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0047 : checkSingleBlackFast (-3, 0) 6064 .south (-7, 5) (-19, -3) = true := by
  decide +kernel

end LangtonsAnt
