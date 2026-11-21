import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0849 : checkSingleBlackFast (-6, 9) 9640 .north (-7, 4) (3, -20) = true := by
  decide +kernel

end LangtonsAnt
