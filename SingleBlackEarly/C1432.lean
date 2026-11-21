import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1432 : checkSingleBlackFast (-23, 0) 24820 .north (-3, 4) (-7, -34) = true := by
  decide +kernel

end LangtonsAnt
