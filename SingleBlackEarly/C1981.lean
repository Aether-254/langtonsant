import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1981 : checkSingleBlackFast (-72, -50) 19547 .east (26, 20) (-7, -38) = true := by
  decide +kernel

end LangtonsAnt
