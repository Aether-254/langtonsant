import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0295 : checkSingleBlackFast (10, 13) 7856 .north (-4, -9) (-20, -11) = true := by
  decide +kernel

end LangtonsAnt
