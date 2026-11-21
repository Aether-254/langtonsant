import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1466 : checkSingleBlackFast (-26, 2) 19392 .south (-3, -7) (-15, -23) = true := by
  decide +kernel

end LangtonsAnt
