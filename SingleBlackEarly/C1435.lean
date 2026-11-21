import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1435 : checkSingleBlackFast (-21, -1) 27304 .north (-2, 4) (-6, -34) = true := by
  decide +kernel

end LangtonsAnt
