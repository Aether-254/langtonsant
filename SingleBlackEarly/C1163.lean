import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1163 : checkSingleBlackFast (26, -20) 11482 .north (-9, 10) (-6, -23) = true := by
  decide +kernel

end LangtonsAnt
