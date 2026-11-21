import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1602 : checkSingleBlackFast (-37, -12) 19711 .east (21, -3) (-22, -39) = true := by
  decide +kernel

end LangtonsAnt
