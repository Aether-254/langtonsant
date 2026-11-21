import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1373 : checkSingleBlackFast (-19, 13) 22336 .north (-2, -5) (-32, -11) = true := by
  decide +kernel

end LangtonsAnt
