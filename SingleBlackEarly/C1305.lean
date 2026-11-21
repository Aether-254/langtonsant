import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1305 : checkSingleBlackFast (-10, 20) 10801 .east (-3, -5) (-25, -20) = true := by
  decide +kernel

end LangtonsAnt
