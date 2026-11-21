import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1484 : checkSingleBlackFast (-24, -4) 19772 .south (-3, -7) (-15, -23) = true := by
  decide +kernel

end LangtonsAnt
