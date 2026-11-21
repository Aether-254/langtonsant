import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1711 : checkSingleBlackFast (-49, -21) 19767 .east (18, 3) (-28, -4) = true := by
  decide +kernel

end LangtonsAnt
