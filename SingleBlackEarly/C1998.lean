import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1998 : checkSingleBlackFast (-73, -48) 21583 .east (39, 18) (-7, -57) = true := by
  decide +kernel

end LangtonsAnt
