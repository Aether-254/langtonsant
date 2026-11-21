import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1218 : checkSingleBlackFast (21, 11) 9780 .south (-8, -2) (-22, -18) = true := by
  decide +kernel

end LangtonsAnt
