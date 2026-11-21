import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1449 : checkSingleBlackFast (-24, 1) 23220 .north (-4, 6) (-10, -34) = true := by
  decide +kernel

end LangtonsAnt
