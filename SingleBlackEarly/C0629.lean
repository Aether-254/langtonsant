import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0629 : checkSingleBlackFast (9, -8) 6740 .north (-4, -1) (-18, -11) = true := by
  decide +kernel

end LangtonsAnt
